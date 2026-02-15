"""
graphplan.py - Planning graph construction.

Replaces: graphplan.cpp core graph-building routines.
"""

from __future__ import annotations
import random
import sys
from typing import Optional, Any

from data_structures import (
    Vertex, HashTable, Operator, CONNECTOR, NOOP, DELETE,
    MAXGOALS, YES, NO, NEW_INSTS,
    is_var, is_const,
)
from pddl_parser import (
    parse_pddl_file, typed_list_to_objects, typed_list_to_type_map,
)
from utilities import (
    make_noop_string, token_list_from_string, instantiate_into_string,
    compare_and_instantiate, undo_instantiations,
    find_all_mutex_ops, find_mutex_facts,
    are_mutex, do_exclusive,
)


# ── Global state (replaces C globals) ────────────────────────────────────────

class PlanningGraph:
    """Encapsulates the full planning-graph state.

    Replaces the C globals: fact_table[], op_table[], goals_at[],
    same_as_prev_flag, bvec_len, etc.
    """

    def __init__(self):
        # Core tables  (indexed by time step)
        self.fact_table: list[HashTable] = []
        self.op_table: list[HashTable] = []
        self.goals_at: list[list[Vertex]] = []

        # Counters
        self.num_created: int = 0
        self.num_deleted: int = 0
        self._uid_counter: int = 0

        # Graph-levelling detection
        self.same_as_prev_flag: bool = False
        self._prev_summary: tuple[int, int] = (0, 0)  # (fact_count, excl_count)

        # Parsed domain/problem data
        self.ops: list[Operator] = []
        self.initial_facts: list[list[str]] = []
        self.the_goals: list[list[str]] = []
        self.the_types: dict[str, str] = {}       # object → type
        self.objects: list[str] = []
        self.predicates: list[dict] = []
        self.constants: list[tuple[list[str], str | None]] = []
        self.negation_predicates: set[str] = set()
        self.domain_name: str = ""
        self.problem_name: str = ""

        # Flags
        self.force_neg_flag: bool = False
        self.debug_flag: int = 0
        self.maxnodes: int = 2048
        self.enable_relevance_pruning: bool = True
        self.relevant_predicates: set[str] = set()

        # Types table for type checking during instantiation
        self.types_table: dict[str, set[str]] = {}  # type → set of objects

    # ── Loading ──────────────────────────────────────────────────────────

    def load(self, domain_file: str, problem_file: str):
        """Parse domain + problem PDDL files and populate internal state."""
        domain = parse_pddl_file(domain_file)
        problem = parse_pddl_file(problem_file)

        self.domain_name = domain['name']
        self.problem_name = problem['name']

        # Build operators from domain actions
        for act in domain['actions']:
            op = Operator()
            op.name = act['name']
            # Flatten params to list of variable names and build type map
            op.params = []
            op._param_types: dict[str, str] = {}
            for names, typ in act['params']:
                for n in names:
                    op.params.append(n)
                    if typ:
                        op._param_types[n] = typ
            op.preconds = act['preconds']
            op.effects = act['effects']
            self.ops.append(op)

        # Predicates
        self.predicates = domain.get('predicates', [])

        # Constants from domain
        self.constants = domain.get('constants', [])

        # Objects from problem  (typed list → flat + type map)
        obj_groups = problem.get('objects', [])
        self.objects = typed_list_to_objects(obj_groups)
        self.the_types = typed_list_to_type_map(obj_groups)

        # Also add constants to objects/types
        for names, typ in self.constants:
            for n in names:
                if n not in self.the_types:
                    self.objects.append(n)
                    self.the_types[n] = typ if typ else 'object'

        # Build types_table  (type → set of objects of that type)
        for obj, typ in self.the_types.items():
            # Handle (either type1 type2 ...) disjunctive types
            if typ and typ.startswith('(either '):
                inner = typ[len('(either '):-1]  # strip parens
                for t in inner.split():
                    t = t.lower()
                    self.types_table.setdefault(t, set()).add(obj)
            else:
                if typ:
                    self.types_table.setdefault(typ, set()).add(obj)
            # everything is also of type 'object'
            self.types_table.setdefault('object', set()).add(obj)

        # Handle types from domain :types section (type hierarchy)
        for names, parent in domain.get('types', []):
            parent_type = parent if parent else 'object'
            for n in names:
                n = n.lower()
                self.types_table.setdefault(n, set())

        # Propagate subtype objects to parent types
        for names, parent in domain.get('types', []):
            parent_type = parent.lower() if parent else 'object'
            for n in names:
                n = n.lower()
                for obj in list(self.types_table.get(n, [])):
                    self.types_table.setdefault(parent_type, set()).add(obj)

        # Initial facts and goals
        self.initial_facts = problem.get('init', [])
        self.the_goals = problem.get('goal', [])

    # ── Data processing (replaces process_data) ──────────────────────────

    def process_data(self):
        """Post-parse normalisation: handle negations, constants, etc."""
        self._process_goals()
        self._process_constants()
        self._process_actions()
        self._prune_irrelevant_actions()
        self._process_initial_facts()

    def _process_goals(self):
        """Replace (not pred ...) goals with bbun_pred ... form."""
        new_goals: list[list[str]] = []
        for g in self.the_goals:
            if g and g[0] == DELETE:
                pred = g[1]
                self.negation_predicates.add(pred)
                new_goals.append([f"bbun{pred}"] + g[2:])
            else:
                new_goals.append(g)
        self.the_goals = new_goals

    def _process_constants(self):
        """Add constant-type facts to initial state."""
        for names, typ in self.constants:
            for name in names:
                if typ:
                    # Add type fact
                    self.initial_facts.append([f"bbconst{name}", name])

    def _process_actions(self):
        """Replace negation in preconditions/effects with bbun_ form."""
        for op in self.ops:
            # Process preconditions
            new_preconds: list = []
            for fact in op.preconds:
                if isinstance(fact, dict):
                    new_preconds.append(fact)
                    continue
                if fact and fact[0] == DELETE:
                    inner = fact[1:]
                    if inner and inner[0] == '=':
                        # inequality - skip or handle
                        continue
                    pred = inner[0]
                    self.negation_predicates.add(pred)
                    new_preconds.append([f"bbun{pred}"] + inner[1:])
                elif fact and fact[0] == '=':
                    # equality - skip
                    continue
                else:
                    new_preconds.append(fact)
            op.preconds = new_preconds

            # Process effects - add dual bbun_ effects for negation predicates
            new_effects: list = []
            for fact in op.effects:
                if isinstance(fact, dict):
                    new_effects.append(fact)
                    continue
                if fact and fact[0] == DELETE:
                    inner = fact[1:]
                    pred = inner[0]
                    new_effects.append(fact)  # keep original delete
                    if pred in self.negation_predicates:
                        # Also add the positive bbun_ fact
                        new_effects.append([f"bbun{pred}"] + inner[1:])
                else:
                    pred = fact[0]
                    new_effects.append(fact)  # keep original
                    if pred in self.negation_predicates:
                        # Also add delete of bbun_ fact
                        new_effects.append([DELETE, f"bbun{pred}"] + fact[1:])
            op.effects = new_effects

    def _process_initial_facts(self):
        """Handle negated initial facts; optionally add implicit negations."""
        has_negation = False
        new_facts: list[list[str]] = []
        for f in self.initial_facts:
            if f and f[0] == DELETE:
                pred = f[1]
                if pred not in self.negation_predicates:
                    self.negation_predicates.add(pred)
                new_facts.append([f"bbun{pred}"] + f[2:])
                has_negation = True
            else:
                new_facts.append(f)
        self.initial_facts = new_facts

        # Add implicit negations if no explicit negation found or forced
        if self.force_neg_flag or not has_negation:
            self._add_negation()

        self._filter_irrelevant_initial_facts()

    def _is_numeric_or_control_symbol(self, token: str) -> bool:
        return token in {
            '=', 'increase', 'decrease', 'assign', 'scale-up', 'scale-down',
            'and', 'or', 'imply', 'when', 'forall', 'exists',
        }

    def _collect_predicates(self, node: Any, out: set[str],
                            include_delete: bool = True):
        """Collect predicate symbols from parser structures conservatively."""
        if isinstance(node, list):
            if not node:
                return
            first = node[0]
            # Container list (list of formulas/facts)
            if not isinstance(first, str):
                for item in node:
                    self._collect_predicates(item, out, include_delete)
                return
            head = first
            if head == DELETE:
                if include_delete and len(node) > 1 and isinstance(node[1], str):
                    out.add(node[1])
                for item in node[1:]:
                    self._collect_predicates(item, out, include_delete)
                return
            if not self._is_numeric_or_control_symbol(head):
                out.add(head)
            for item in node[1:]:
                self._collect_predicates(item, out, include_delete)
            return
        if isinstance(node, dict):
            for value in node.values():
                self._collect_predicates(value, out, include_delete)
            return
        if isinstance(node, tuple):
            for value in node:
                self._collect_predicates(value, out, include_delete)
            return

    def _predicates_in(self, formulas: list, include_delete: bool = True) -> set[str]:
        preds: set[str] = set()
        self._collect_predicates(formulas, preds, include_delete=include_delete)
        return preds

    def _prune_irrelevant_actions(self):
        """Backward relevance pruning over action schemas (complete-safe)."""
        if not self.enable_relevance_pruning:
            return
        if not self.ops:
            return

        goal_preds = self._predicates_in(self.the_goals, include_delete=True)
        if not goal_preds:
            return

        op_infos: list[dict[str, Any]] = []
        for op in self.ops:
            add_preds = self._predicates_in(op.effects, include_delete=False)
            pre_preds = self._predicates_in(op.preconds, include_delete=True)
            has_complex = any(isinstance(x, dict) for x in op.preconds) or \
                any(isinstance(x, dict) for x in op.effects)
            op_infos.append({
                'op': op,
                'add_preds': add_preds,
                'pre_preds': pre_preds,
                'always_keep': has_complex,
            })

        relevant_preds = set(goal_preds)
        relevant_idx: set[int] = set()
        changed = True
        while changed:
            changed = False
            for idx, info in enumerate(op_infos):
                if idx in relevant_idx:
                    continue
                if info['always_keep'] or (info['add_preds'] & relevant_preds):
                    relevant_idx.add(idx)
                    before = len(relevant_preds)
                    relevant_preds |= info['pre_preds']
                    if len(relevant_preds) != before:
                        changed = True
                    changed = True

        old_count = len(self.ops)
        self.ops = [
            info['op'] for idx, info in enumerate(op_infos) if idx in relevant_idx
        ]
        self.relevant_predicates = relevant_preds

        if self.debug_flag >= 1:
            print(f"  Relevance pruning: {old_count} -> {len(self.ops)} actions, "
                  f"{len(self.relevant_predicates)} predicates")

    def _filter_irrelevant_initial_facts(self):
        """Drop initial facts with predicates outside the relevance closure."""
        if not self.relevant_predicates:
            return

        filtered: list[list[str]] = []
        for fact in self.initial_facts:
            if not fact:
                continue
            pred = fact[1] if fact[0] == DELETE and len(fact) > 1 else fact[0]
            if pred in self.relevant_predicates:
                filtered.append(fact)
        self.initial_facts = filtered

    def _add_negation(self):
        """Add implicit negative initial facts for negation predicates."""
        # Build set of initial fact strings for quick lookup
        init_set: set[str] = set()
        for f in self.initial_facts:
            init_set.add(CONNECTOR.join(f))

        for pred in self.negation_predicates:
            if self.relevant_predicates and f"bbun{pred}" not in self.relevant_predicates:
                continue
            # Get arity from predicates list
            arity = self._get_predicate_arity(pred)
            if arity == 1:
                for obj in self.objects:
                    fact_key = CONNECTOR.join([pred, obj])
                    if fact_key not in init_set:
                        self.initial_facts.append([f"bbun{pred}", obj])

    def _get_predicate_arity(self, pred_name: str) -> int:
        """Return number of parameters for a predicate."""
        for p in self.predicates:
            if p['name'] == pred_name:
                count = 0
                for names, _ in p['params']:
                    count += len(names)
                return count
        return 0

    # ── Graph construction ───────────────────────────────────────────────

    def create_graph(self, max_time: int, auto_stop: bool = True) -> int:
        """Build the planning graph up to *max_time* layers.

        Returns the time step at which goals are reachable and non-mutex,
        or ``-1`` if unsolvable.
        """
        # Allocate tables
        self.fact_table = [HashTable() for _ in range(max_time + 2)]
        self.op_table = [HashTable() for _ in range(max_time + 1)]
        self.goals_at = [[] for _ in range(max_time + 2)]
        self._uid_counter = 0

        # Insert initial facts
        for fact_tokens in self.initial_facts:
            name = CONNECTOR.join(fact_tokens)
            v = self.fact_table[0].insert(name)
            v.is_true = 1
            v.rand1 = random.randint(1, 2**31)
            v.uid_index = self._uid_counter
            self._uid_counter += 1

        self.same_as_prev_flag = False
        self._prev_summary = (0, 0)

        for time in range(max_time):
            if auto_stop and self.can_stop(time):
                return time
            if self.same_as_prev_flag:
                if auto_stop:
                    return -1   # graph levelled, goals still not reachable
                self._make_copy(time)
            else:
                self._create_graph_layer(time)

        if self.can_stop(max_time):
            return max_time
        return -1

    def extend_graph(self, old_time: int, new_max: int) -> int:
        """Extend an existing graph from *old_time* to *new_max*.

        Used when iteratively deepening.  Returns new solvable time or -1.
        """
        # Ensure tables are large enough
        while len(self.fact_table) <= new_max + 1:
            self.fact_table.append(HashTable())
        while len(self.op_table) <= new_max:
            self.op_table.append(HashTable())
        while len(self.goals_at) <= new_max + 1:
            self.goals_at.append([])

        for time in range(old_time, new_max):
            if self.same_as_prev_flag:
                self._make_copy(time)
            else:
                self._create_graph_layer(time)

        if self.can_stop(new_max):
            return new_max
        return -1

    def _create_graph_layer(self, time: int):
        """Build a single graph layer at *time* → *time+1*."""

        # 1. Carry forward facts from time to time+1 (persistence)
        for v in self.fact_table[time]:
            w = self.fact_table[time + 1].insert(v.name)
            v.next_time = w
            w.prev_time = v

        # 2. Instantiate operators
        current_facts = list(self.fact_table[time])
        fact_tokens_list = [(v.name, token_list_from_string(v.name))
                           for v in current_facts]

        for op in self.ops:
            self._do_operator(op, fact_tokens_list, time)

        # 3. Create NOOP layer
        self._make_noop_layer(time)

        # 4. Assign UIDs to operators
        for v in self.op_table[time]:
            v.uid_index = self._uid_counter
            self._uid_counter += 1

        # 5. Assign UIDs & random values to new facts
        for v in self.fact_table[time + 1]:
            if v.uid_index < 0:
                v.uid_index = self._uid_counter
                self._uid_counter += 1
            v.rand1 = random.randint(1, 2**31)

        # 6. Compute mutual exclusions
        find_all_mutex_ops(self.op_table[time], self.fact_table[time],
                          self.fact_table[time + 1], time)
        fcount, ecount = find_mutex_facts(self.fact_table[time + 1])

        # 7. Check for graph levelling
        summary = (fcount, ecount)
        if summary == self._prev_summary and time > 0:
            self.same_as_prev_flag = True
        self._prev_summary = summary

    def _make_noop_layer(self, time: int):
        """Create persistence (NOOP) actions for each fact at *time*."""
        for v in self.fact_table[time]:
            w = v.next_time
            if w is None:
                continue
            noop_name = make_noop_string(v.name)
            noop = self.op_table[time].insert(noop_name)
            noop.is_noop = 1
            # precondition edge: fact[t] → noop
            noop.in_edges.append(v)
            v.out_edges.append(noop)
            # effect edge: noop → fact[t+1]
            noop.out_edges.append(w)
            w.in_edges.append(noop)

    def _do_operator(self, op: Operator, fact_tokens: list[tuple[str, list[str]]],
                     time: int):
        """Recursively instantiate *op* against facts at *time*."""
        # Filter to non-quantified, non-dict preconditions
        preconds = [p for p in op.preconds if isinstance(p, list)]
        if not preconds:
            return
        insts: dict[str, str] = {}
        self._do_operator_rec(op, preconds, 0, fact_tokens, insts, time)

    def _do_operator_rec(self, op: Operator, preconds: list[list[str]],
                         prec_idx: int, fact_tokens: list[tuple[str, list[str]]],
                         insts: dict[str, str], time: int):
        """Recursive backtracking instantiation of operator preconditions."""
        if prec_idx >= len(preconds):
            # All preconditions matched → check parameters and create graph piece
            # First check if all operator parameters are bound
            all_bound = all(p in insts for p in op.params if is_var(p))
            if all_bound:
                self._make_graph_piece(op, insts, time)
            else:
                # Try to bind remaining params from type constraints
                self._bind_remaining_params(op, insts, fact_tokens, time)
            return

        pattern = preconds[prec_idx]
        # Substitute known bindings
        inst_pattern = [insts.get(t, t) if is_var(t) else t for t in pattern]

        # Check if fully ground
        if all(is_const(t) for t in inst_pattern):
            name = CONNECTOR.join(inst_pattern)
            if self.fact_table[time].lookup(name) is not None:
                self._do_operator_rec(op, preconds, prec_idx + 1,
                                      fact_tokens, insts, time)
            return

        # Try to match against all current facts
        pattern_vars = {tok for tok in inst_pattern if is_var(tok)}
        for _, fact_toks in fact_tokens:
            newly_bound = [v for v in pattern_vars if v not in insts]
            result = compare_and_instantiate(inst_pattern, fact_toks, insts)
            if result != NO:
                # Type check: verify new bindings are type-consistent
                if self._check_type_consistency(op, insts):
                    self._do_operator_rec(op, preconds, prec_idx + 1,
                                          fact_tokens, insts, time)
                # Backtrack only variables introduced at this level.
                for v in newly_bound:
                    insts.pop(v, None)

    def _check_type_consistency(self, op: Operator, insts: dict[str, str]) -> bool:
        """Verify that all bindings in *insts* are consistent with
        the operator's declared parameter types."""
        if not hasattr(op, '_param_types') or not op._param_types:
            return True  # STRIPS domain: no declared types
        for var, val in insts.items():
            declared_type = op._param_types.get(var)
            if declared_type is None:
                continue  # no type constraint
            declared_type = declared_type.lower()
            # Handle (either t1 t2 ...)
            if declared_type.startswith('(either '):
                inner = declared_type[len('(either '):-1]
                allowed_types = inner.split()
            else:
                allowed_types = [declared_type]
            # Check if val belongs to any of the allowed types
            ok = False
            for t in allowed_types:
                if val in self.types_table.get(t, set()):
                    ok = True
                    break
            if not ok:
                # Also check 'object' as fallback
                if val not in self.types_table.get('object', set()):
                    return False
                # val exists but not of the right type
                return False
        return True

    def _bind_remaining_params(self, op: Operator, insts: dict[str, str],
                               fact_tokens: list[tuple[str, list[str]]],
                               time: int):
        """Bind unbound parameters using type constraints."""
        unbound = [p for p in op.params if is_var(p) and p not in insts]
        if not unbound:
            self._make_graph_piece(op, insts, time)
            return

        var = unbound[0]
        typ = op._param_types.get(var, 'object')
        if typ:
            typ = typ.lower()

        # Get candidates from types_table, handling (either ...) types
        if typ and typ.startswith('(either '):
            inner = typ[len('(either '):-1]
            candidates: set[str] = set()
            for t in inner.split():
                candidates |= self.types_table.get(t, set())
        else:
            candidates = self.types_table.get(typ, set()) if typ else set()
        if not candidates:
            candidates = set(self.objects)

        for obj in candidates:
            insts[var] = obj
            self._bind_remaining_params(op, insts, fact_tokens, time)
            del insts[var]

    def _make_graph_piece(self, op: Operator, insts: dict[str, str], time: int):
        """Insert an instantiated operator into the graph at *time*."""
        # Build ground operator name
        params_flat = []
        for p in op.params:
            if is_var(p):
                params_flat.append(insts.get(p, p))
            else:
                params_flat.append(p)
        op_name = CONNECTOR.join([op.name] + params_flat)

        # Check for duplicate
        if self.op_table[time].lookup(op_name) is not None:
            return

        # Check: illegal match (same var bound to different constants)
        # (already handled by backtracking, but double-check)

        # Check max nodes
        if len(self.op_table[time]) >= self.maxnodes:
            return

        # Check preconditions are non-mutex
        prec_verts: list[Vertex] = []
        for prec in op.preconds:
            if isinstance(prec, dict):
                continue
            prec_tokens = [insts.get(t, t) if is_var(t) else t for t in prec]
            prec_name = CONNECTOR.join(prec_tokens)
            pv = self.fact_table[time].lookup(prec_name)
            if pv is None:
                return  # precondition not in current layer
            prec_verts.append(pv)

        # Check pairwise non-mutex of preconditions
        for i in range(len(prec_verts)):
            for j in range(i + 1, len(prec_verts)):
                if are_mutex(prec_verts[i], prec_verts[j]):
                    return  # mutex preconditions → skip

        # Create operator vertex
        op_vert = self.op_table[time].insert(op_name)
        self.num_created += 1

        # Connect preconditions → operator
        for pv in prec_verts:
            op_vert.in_edges.append(pv)
            pv.out_edges.append(op_vert)

        # Process effects
        for eff in op.effects:
            if isinstance(eff, dict):
                continue
            eff_tokens = [insts.get(t, t) if is_var(t) else t for t in eff]

            if eff_tokens and eff_tokens[0] == DELETE:
                # Delete effect
                del_name = CONNECTOR.join(eff_tokens[1:])
                op_vert.del_list.append(del_name)
                # Create del_edge to fact in next time step
                del_fact = self.fact_table[time + 1].lookup(del_name)
                if del_fact is not None:
                    op_vert.del_edges.append(del_fact)
            else:
                # Positive effect: ensure fact exists in next layer
                eff_name = CONNECTOR.join(eff_tokens)
                w = self.fact_table[time + 1].insert(eff_name)
                op_vert.out_edges.append(w)
                w.in_edges.append(op_vert)

    def _make_copy(self, time: int):
        """Copy a levelled layer (graph has stabilised)."""
        prev_op = self.op_table[time - 1] if time > 0 else HashTable()
        prev_fact_next = self.fact_table[time]

        # Carry forward facts
        for v in self.fact_table[time]:
            w = self.fact_table[time + 1].insert(v.name)
            v.next_time = w
            w.prev_time = v
            w.rand1 = random.randint(1, 2**31)
            if v.uid_index >= 0:
                w.uid_index = self._uid_counter
                self._uid_counter += 1

        # Copy operators
        for old_op in prev_op:
            new_op = self.op_table[time].insert(old_op.name)
            new_op.is_noop = old_op.is_noop
            new_op.uid_index = self._uid_counter
            self._uid_counter += 1

            # Reconnect in_edges to facts at time
            for old_prec in old_op.in_edges:
                new_prec = self.fact_table[time].lookup(old_prec.name)
                if new_prec:
                    new_op.in_edges.append(new_prec)
                    new_prec.out_edges.append(new_op)

            # Reconnect out_edges to facts at time+1
            for old_eff in old_op.out_edges:
                new_eff = self.fact_table[time + 1].lookup(old_eff.name)
                if new_eff:
                    new_op.out_edges.append(new_eff)
                    new_eff.in_edges.append(new_op)

            # Copy del_list and del_edges
            new_op.del_list = list(old_op.del_list)
            for old_del in old_op.del_edges:
                new_del = self.fact_table[time + 1].lookup(old_del.name)
                if new_del:
                    new_op.del_edges.append(new_del)

        # Copy exclusions for operators
        for old_op in prev_op:
            new_op = self.op_table[time].lookup(old_op.name)
            if new_op is None:
                continue
            for excl_op in old_op.exclusive:
                new_excl = self.op_table[time].lookup(excl_op.name)
                if new_excl and new_excl.uid_index not in new_op.exclusive_set:
                    do_exclusive(new_op, new_excl)

        # Copy exclusions for facts
        for old_fact in self.fact_table[time]:
            new_fact = self.fact_table[time + 1].lookup(old_fact.name)
            if new_fact is None:
                continue
            for excl_fact in old_fact.exclusive:
                new_excl = self.fact_table[time + 1].lookup(excl_fact.name)
                if new_excl and new_excl.uid_index not in new_fact.exclusive_set:
                    do_exclusive(new_fact, new_excl)

    # ── Stopping check ───────────────────────────────────────────────────

    def can_stop(self, time: int) -> bool:
        """Check if all goals reachable and pairwise non-mutex at *time*."""
        goal_verts: list[Vertex] = []
        for g in self.the_goals:
            name = CONNECTOR.join(g)
            v = self.fact_table[time].lookup(name)
            if v is None:
                return False
            goal_verts.append(v)

        # Check pairwise non-mutex
        for i in range(len(goal_verts)):
            for j in range(i + 1, len(goal_verts)):
                if are_mutex(goal_verts[i], goal_verts[j]):
                    return False

        return True

    def setup_goals(self, time: int) -> int:
        """Populate ``goals_at[time]`` and mark initial facts.

        Returns the number of goals.
        """
        self.goals_at[time] = []
        for g in self.the_goals:
            name = CONNECTOR.join(g)
            v = self.fact_table[time].lookup(name)
            if v is not None:
                self.goals_at[time].append(v)

        # Mark initial facts as true
        for v in self.fact_table[0]:
            v.is_true = 1

        return len(self.goals_at[time])
