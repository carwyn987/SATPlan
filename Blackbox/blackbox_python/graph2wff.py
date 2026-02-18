"""
graph2wff.py - SAT encoding of the planning graph.

Replaces: graph2wff.cpp

Converts the layered planning graph into a CNF formula in clause-list form,
then optionally writes DIMACS format for external SAT solvers.
"""

from __future__ import annotations
from typing import Optional

from data_structures import (
    Vertex, HashTable,
    BB_OutputOpMutex, BB_OutputOpPre, BB_OutputFactFrame,
    BB_OutputFactMutex, BB_OutputOpEffect, BB_OutputRedundant,
    BB_OutputOpPreOp, BB_OutputActDefs,
    PrintLit, PrintCNF, PrintExit, PrintMap, PrintModel,
    NOOP, CONNECTOR,
)
from graphplan import PlanningGraph
from utilities import are_mutex


# ── Axiom presets ────────────────────────────────────────────────────────────

AXIOM_PRESETS = {
    7:   BB_OutputOpMutex | BB_OutputOpPre | BB_OutputFactFrame,                # default
    15:  BB_OutputOpMutex | BB_OutputOpPre | BB_OutputFactFrame | BB_OutputFactMutex,  # mutex
    31:  BB_OutputOpMutex | BB_OutputOpPre | BB_OutputFactFrame | BB_OutputFactMutex | BB_OutputOpEffect,  # compressed
    63:  BB_OutputOpMutex | BB_OutputOpPre | BB_OutputFactFrame | BB_OutputFactMutex | BB_OutputOpEffect | BB_OutputRedundant,  # expanded
    129: BB_OutputOpPreOp | BB_OutputActDefs,                                   # action
}


class SATEncoder:
    """Encodes a planning graph as a CNF SAT formula."""

    def __init__(self, graph: PlanningGraph, axioms: int = 7,
                 printflag: int = 0):
        self.graph = graph
        self.axioms = axioms
        self.printflag = printflag

        # Propositional variables
        self.numvar: int = 0
        self.numclause: int = 0
        self.clauses: list[list[int]] = []
        self.prop2vertex: list[Optional[Vertex]] = [None]  # 1-indexed
        self.num_action_vars: int = 0
        self.num_fluent_vars: int = 0
        self.goal_assumptions: list[int] = []
        # Stable mapping used by incremental SAT across horizons.
        self._uid_to_var: dict[int, int] = {}
        # Track last encoded time layer for incremental skip optimisation.
        self._prev_maxtime: int = 0

    # ── Main entry point ─────────────────────────────────────────────────

    def encode(self, maxtime: int, num_goals: int,
               incremental: bool = False) -> tuple[list[list[int]], int, int]:
        """Encode the planning graph to CNF.

        Returns ``(clauses, numvar, numclause)`` where each clause is a
        list of integer literals (positive or negative variable numbers).
        """
        self.clauses = []
        self.numclause = 0
        self.goal_assumptions = []

        if not incremental:
            self.numvar = 0
            self.prop2vertex = [None]
            self._uid_to_var = {}
            self._prev_maxtime = 0

        # Mark vertices to encode.
        if incremental:
            # Incremental SAT requires monotone CNF growth across horizons.
            # Use all vertices in layers <= maxtime to prevent horizon-specific
            # backward-pruning from changing old clauses.
            self._mark_all_needed(maxtime)
        else:
            self._remove_unneeded(maxtime)

        # Assign propositional variables
        acts_only = bool(self.axioms & BB_OutputOpPreOp)
        self._assign_props(maxtime, num_goals, acts_only, incremental=incremental)

        # In incremental mode, only emit initial-state clauses on the first call.
        if incremental and self._prev_maxtime == 0 and (self.axioms & BB_OutputOpPre):
            self._generate_initial_state()

        # Determine which layers to encode: skip already-encoded ones in
        # incremental mode.
        start_layer = self._prev_maxtime if incremental else 0

        # Generate axioms for each time layer
        for t in range(start_layer, maxtime):
            op_table = self.graph.op_table[t]
            fact_table = self.graph.fact_table[t]
            fact_table_next = self.graph.fact_table[t + 1]

            if self.axioms & BB_OutputActDefs:
                self._generate_actdefs(op_table)

            if self.axioms & BB_OutputOpPre:
                self._generate_precond(op_table)

            if self.axioms & BB_OutputOpEffect:
                self._generate_effect(op_table)

            if self.axioms & BB_OutputFactFrame:
                # For incremental SAT, keep the frame encoding monotone by
                # avoiding last-layer simplification.
                is_last = (t == maxtime - 1) and not incremental
                self._generate_frame(fact_table_next, simplified=is_last)

            if self.axioms & BB_OutputOpMutex:
                self._generate_op_mutex(op_table, incremental=incremental)

            if self.axioms & BB_OutputFactMutex:
                self._generate_fact_mutex(fact_table_next)

            if self.axioms & BB_OutputOpPreOp:
                self._generate_op_pre_op(op_table, fact_table)

        if incremental:
            self._prev_maxtime = maxtime

        # Initial state unit clauses
        if (self.axioms & BB_OutputOpPre) and not incremental:
            self._generate_initial_state()

        # Goal state unit clauses
        if self.axioms & BB_OutputFactFrame:
            if incremental:
                self.goal_assumptions = [
                    gv.prop for gv in self.graph.goals_at[maxtime]
                    if gv.prop != 0
                ]
            else:
                self._generate_goal_state(maxtime, num_goals)

        self.numclause = len(self.clauses)
        return self.clauses, self.numvar, self.numclause

    # ── Variable assignment ──────────────────────────────────────────────

    def _assign_props(self, maxtime: int, num_goals: int, acts_only: bool,
                      incremental: bool = False):
        """Assign propositional variable numbers to graph vertices."""
        if not incremental:
            self.numvar = 0
            self.prop2vertex = [None]  # index 0 unused (1-based)
            self._uid_to_var = {}

        action_count = 0
        fluent_count = 0

        def ensure_var(v: Vertex) -> int:
            nonlocal action_count, fluent_count
            if not incremental:
                self.numvar += 1
                v.prop = self.numvar
                self.prop2vertex.append(v)
                return v.prop
            uid = v.uid_index if v.uid_index >= 0 else id(v)
            existing = self._uid_to_var.get(uid)
            if existing is not None:
                v.prop = existing
                return existing
            self.numvar += 1
            v.prop = self.numvar
            self._uid_to_var[uid] = self.numvar
            self.prop2vertex.append(v)
            return v.prop

        # Assign to operators (action layers)
        for t in range(maxtime):
            for v in self.graph.op_table[t]:
                if v.needed:
                    ensure_var(v)
                    action_count += 1

        # Assign to facts (unless action-only encoding)
        if not acts_only:
            for t in range(maxtime + 1):
                for v in self.graph.fact_table[t]:
                    if v.needed:
                        ensure_var(v)
                        fluent_count += 1

        self.num_action_vars = action_count
        self.num_fluent_vars = fluent_count

    # ── Backward reachability (mark needed vertices) ─────────────────────

    def _remove_unneeded(self, maxtime: int):
        """Mark only vertices reachable backward from goals as needed."""
        # Reset all
        for t in range(maxtime + 1):
            for v in self.graph.fact_table[t]:
                v.needed = 0
        for t in range(maxtime):
            for v in self.graph.op_table[t]:
                v.needed = 0

        # Mark goals
        for gv in self.graph.goals_at[maxtime]:
            gv.needed = 1

        # Backward propagation
        for t in range(maxtime, 0, -1):
            # For each needed fact at time t, mark its producers as needed
            for fv in self.graph.fact_table[t]:
                if not fv.needed:
                    continue
                for op in fv.in_edges:
                    op.needed = 1

            # For each needed operator at time t-1, mark its preconditions
            for ov in self.graph.op_table[t - 1]:
                if not ov.needed:
                    continue
                for prec in ov.in_edges:
                    prec.needed = 1

        # Mark initial facts
        for v in self.graph.fact_table[0]:
            if v.needed:
                pass  # already marked

    def _mark_all_needed(self, maxtime: int):
        """Mark every fact/op up to *maxtime* as needed (monotone encoding)."""
        for t, fact_table in enumerate(self.graph.fact_table):
            needed = 1 if t <= maxtime else 0
            for v in fact_table:
                v.needed = needed
        for t, op_table in enumerate(self.graph.op_table):
            needed = 1 if t < maxtime else 0
            for v in op_table:
                v.needed = needed

    # ── Axiom generators ─────────────────────────────────────────────────

    def _generate_precond(self, op_table: HashTable):
        """action → preconditions: (NOT action) OR fact."""
        for op in op_table:
            if not op.needed or op.prop == 0:
                continue
            for prec in op.in_edges:
                if prec.prop == 0:
                    continue
                self.clauses.append([-op.prop, prec.prop])

    def _generate_frame(self, fact_table: HashTable, simplified: bool = False):
        """Frame axioms: fact must have at least one producer.

        Normal: ``(NOT fact_t) OR producer1 OR producer2 OR ...``
        Simplified (last layer): ``producer1 OR producer2 OR ...``
        """
        for fv in fact_table:
            if not fv.needed or fv.prop == 0:
                continue
            producers = [op for op in fv.in_edges if op.needed and op.prop != 0]
            if not producers:
                continue
            if simplified:
                clause = [op.prop for op in producers]
            else:
                clause = [-fv.prop] + [op.prop for op in producers]
            if clause:
                self.clauses.append(clause)

    # ── Auxiliary variable allocation ────────────────────────────────────

    def _next_aux_var(self) -> int:
        """Allocate a fresh auxiliary SAT variable (not tied to any vertex)."""
        self.numvar += 1
        self.prop2vertex.append(None)
        return self.numvar

    # ── AMO ladder encoding ──────────────────────────────────────────────

    def _amo_ladder(self, lits: list[int]):
        """At-most-one constraint via ladder/commander encoding.

        For k literals emits 3(k-1)-1 clauses using k-1 auxiliary variables,
        compared to k(k-1)/2 for pairwise.  Falls back to pairwise for k<=3.
        """
        k = len(lits)
        if k <= 1:
            return
        if k <= 3:
            # Pairwise is same cost or cheaper for small k
            for i in range(k):
                for j in range(i + 1, k):
                    self.clauses.append([-lits[i], -lits[j]])
            return

        # Ladder encoding: auxiliary variables a_1 .. a_{k-1}
        aux = [self._next_aux_var() for _ in range(k - 1)]

        # First rung: x_0 => a_0
        self.clauses.append([-lits[0], aux[0]])

        for i in range(1, k - 1):
            # x_i => a_i  (if x_i is true, ladder must be on from here)
            self.clauses.append([-lits[i], aux[i]])
            # a_{i-1} => a_i  (ladder propagation)
            self.clauses.append([-aux[i - 1], aux[i]])
            # NOT(x_i AND a_{i-1})  (at most one: can't pick x_i if ladder already on)
            self.clauses.append([-lits[i], -aux[i - 1]])

        # Last rung: NOT(x_{k-1} AND a_{k-2})
        self.clauses.append([-lits[k - 1], -aux[k - 2]])

    # ── Mutex clique finding ─────────────────────────────────────────────

    @staticmethod
    def _find_mutex_cliques(ops: list[Vertex]) -> tuple[list[list[int]], list[tuple[int, int]]]:
        """Greedy clique cover over the mutex graph of *ops*.

        Returns ``(cliques, leftover_edges)`` where each clique is a list of
        indices into *ops*, and leftover_edges are mutex pairs not covered by
        any clique.
        """
        n = len(ops)
        # Build adjacency using prop-based identity
        prop_to_idx = {ops[i].prop: i for i in range(n)}
        adj: list[set[int]] = [set() for _ in range(n)]
        all_edges: set[tuple[int, int]] = set()

        for i in range(n):
            for excl in ops[i].exclusive:
                if not excl.needed or excl.prop == 0:
                    continue
                j = prop_to_idx.get(excl.prop)
                if j is not None and j != i:
                    edge = (min(i, j), max(i, j))
                    if edge not in all_edges:
                        all_edges.add(edge)
                        adj[i].add(j)
                        adj[j].add(i)

        covered_edges: set[tuple[int, int]] = set()
        cliques: list[list[int]] = []
        remaining = set(range(n))

        while remaining:
            # Pick vertex with highest degree in remaining graph
            seed = max(remaining, key=lambda x: len(adj[x] & remaining))
            if not (adj[seed] & remaining):
                break  # no more edges

            # Grow maximal clique from seed
            clique = [seed]
            candidates = adj[seed] & remaining
            for c in sorted(candidates, key=lambda x: -len(adj[x] & candidates)):
                if all(c in adj[m] for m in clique):
                    clique.append(c)

            if len(clique) < 2:
                break

            # Record covered edges
            for a in range(len(clique)):
                for b in range(a + 1, len(clique)):
                    edge = (min(clique[a], clique[b]), max(clique[a], clique[b]))
                    covered_edges.add(edge)

            cliques.append(clique)

            # Remove clique members from remaining
            for m in clique:
                remaining.discard(m)

        leftover = [e for e in all_edges if e not in covered_edges]
        return cliques, leftover

    # ── Operator mutex generation ────────────────────────────────────────

    def _generate_op_mutex(self, op_table: HashTable, incremental: bool = False):
        """Operator mutual exclusion via AMO ladder encoding.

        For incremental SAT, falls back to pairwise encoding since auxiliary
        variable IDs would be unstable across horizons.
        """
        # Collect needed ops with assigned props
        ops = [op for op in op_table if op.needed and op.prop != 0]
        if not ops:
            return

        if incremental:
            # Pairwise fallback for incremental mode
            seen: set[tuple[int, int]] = set()
            for op in ops:
                for excl_op in op.exclusive:
                    if not excl_op.needed or excl_op.prop == 0:
                        continue
                    pair = (min(op.prop, excl_op.prop), max(op.prop, excl_op.prop))
                    if pair not in seen:
                        seen.add(pair)
                        self.clauses.append([-op.prop, -excl_op.prop])
            return

        # Non-incremental: use clique-based AMO ladder encoding
        cliques, leftover = self._find_mutex_cliques(ops)

        for clique_indices in cliques:
            lits = [ops[i].prop for i in clique_indices]
            self._amo_ladder(lits)

        # Emit pairwise for leftover edges not covered by cliques
        for i, j in leftover:
            self.clauses.append([-ops[i].prop, -ops[j].prop])

    def _generate_fact_mutex(self, fact_table: HashTable):
        """Fact mutual exclusion: (NOT f1) OR (NOT f2)."""
        seen: set[tuple[int, int]] = set()
        for fv in fact_table:
            if not fv.needed or fv.prop == 0:
                continue
            for excl_fv in fv.exclusive:
                if not excl_fv.needed or excl_fv.prop == 0:
                    continue
                pair = (min(fv.prop, excl_fv.prop), max(fv.prop, excl_fv.prop))
                if pair in seen:
                    continue
                seen.add(pair)
                self.clauses.append([-fv.prop, -excl_fv.prop])

    def _generate_effect(self, op_table: HashTable):
        """action → effects: (NOT action) OR effect / (NOT action) OR (NOT del)."""
        for op in op_table:
            if not op.needed or op.prop == 0:
                continue
            # Positive effects
            for eff in op.out_edges:
                if eff.needed and eff.prop != 0:
                    self.clauses.append([-op.prop, eff.prop])
            # Delete effects
            for del_v in op.del_edges:
                if del_v.needed and del_v.prop != 0:
                    self.clauses.append([-op.prop, -del_v.prop])

    def _generate_actdefs(self, op_table: HashTable):
        """Action definitions for DAGSat: action ∨ ¬prec₁ ∨ … ∨ ¬eff₁ ∨ …"""
        for op in op_table:
            if not op.needed or op.prop == 0:
                continue
            clause = [op.prop]
            for prec in op.in_edges:
                if prec.prop != 0:
                    clause.append(-prec.prop)
            for eff in op.out_edges:
                if eff.prop != 0:
                    clause.append(-eff.prop)
            for del_v in op.del_edges:
                if del_v.prop != 0:
                    clause.append(del_v.prop)
            self.clauses.append(clause)

    def _generate_op_pre_op(self, op_table: HashTable, fact_table: HashTable):
        """Operator-precondition-operator chaining axioms.

        For each fact, if it's a precondition of op2 and an effect of op1:
        ``(NOT op2) OR op1_1 OR op1_2 OR ...``
        """
        for fv in fact_table:
            if not fv.needed:
                continue
            producers = [op for op in fv.in_edges if op.needed and op.prop != 0]
            if not producers:
                continue
            for consumer in fv.out_edges:
                if not consumer.needed or consumer.prop == 0:
                    continue
                clause = [-consumer.prop] + [p.prop for p in producers]
                self.clauses.append(clause)

    # ── Initial / goal state ─────────────────────────────────────────────

    def _generate_initial_state(self):
        """Add unit clauses for initial true facts."""
        for v in self.graph.fact_table[0]:
            if v.needed and v.prop != 0 and v.is_true:
                self.clauses.append([v.prop])

    def _generate_goal_state(self, maxtime: int, num_goals: int):
        """Add unit clauses for goal facts at final time."""
        for gv in self.graph.goals_at[maxtime]:
            if gv.prop != 0:
                self.clauses.append([gv.prop])

    def get_goal_assumptions(self) -> list[int]:
        """Return goal literals for assumption-based incremental solving."""
        return list(self.goal_assumptions)

    # ── Solution → graph ─────────────────────────────────────────────────

    def soln2graph(self, soln: list[int]):
        """Map SAT solution back to graph vertices.

        *soln* is indexed 1..numvar (soln[0] unused). Value 1 = true, 0 = false.
        """
        for i in range(1, self.numvar + 1):
            v = self.prop2vertex[i]
            if v is not None:
                v.used = soln[i] if i < len(soln) else 0

    # ── DIMACS output ────────────────────────────────────────────────────

    def to_dimacs(self) -> str:
        """Return the CNF formula as a DIMACS-format string."""
        lines = [f"p cnf {self.numvar} {self.numclause}"]
        for clause in self.clauses:
            lines.append(' '.join(str(lit) for lit in clause) + ' 0')
        return '\n'.join(lines) + '\n'

    def print_variable_map(self):
        """Print the mapping from variable numbers to vertex names."""
        for i in range(1, self.numvar + 1):
            v = self.prop2vertex[i]
            if v is not None:
                print(f"  {i}: {v.name}")
