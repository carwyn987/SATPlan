import sys
from unified_planning.io import PDDLReader
from unified_planning.model.operators import OperatorKind
import re
import keyword
# --- your SATPlan infra ---
from planning import PlanningProblem, Action, SATPlan
from logic import cdcl_satisfiable  # or dpll_satisfiable

PYTHON_KEYWORDS = {
    "in", "is", "and", "or", "not", "if", "else", "for", "while", "def",
    "class", "return", "lambda", "from", "import", "pass", "break", "continue",
    "try", "except", "finally", "with", "as", "yield", "global", "nonlocal",
    "assert", "del", "raise", "True", "False", "None"
}

def safe_pred_name(name: str) -> str:
    # Capitalize so ~Pred(...) parses correctly in many AIMA-style expr() parsers
    out = name[:1].upper() + name[1:]
    # Avoid python keywords (notably "in")
    if name in PYTHON_KEYWORDS or out in PYTHON_KEYWORDS:
        out = out + "_p"
    return out

def atom_str_from_parts(pred: str, args: list[str]) -> str:
    pred = safe_pred_name(pred)
    args = [sanitize_ident(a) for a in args]
    return f"{pred}({', '.join(args)})"

def is_neg_lit(s: str) -> bool:
    return s.startswith("~")

def lit_atom(s: str) -> str:
    return s[1:] if is_neg_lit(s) else s
def sanitize_ident(name: str) -> str:
    """
    Turn PDDL identifiers into expr()-safe identifiers:
    - replace non [A-Za-z0-9_] with '_'
    - avoid starting with a digit
    - avoid Python keywords
    """
    s = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if s and s[0].isdigit():
        s = "v_" + s
    if keyword.iskeyword(s):
        s = s + "_p"
    return s

def safe_pred_name(name: str) -> str:
    # capitalize predicates to play nice with your expr() conventions
    s = sanitize_ident(name)
    return s[:1].upper() + s[1:] if s else s

# --- Stringification helpers: UP expressions -> your '&' / '~' / Pred(args) syntax ---

def _atom_to_str(node) -> str:
    if node.is_fluent_exp():
        name = safe_pred_name(node.fluent().name)
        args = []
        for a in node.args:
            if a.is_object_exp():
                args.append(sanitize_ident(a.object().name))
            elif a.is_parameter_exp():
                args.append(sanitize_ident(a.parameter().name))
            else:
                args.append(sanitize_ident(str(a)))
        return f"{name}({', '.join(args)})"
    raise ValueError(f"Expected fluent atom, got: {node}")



def expr_to_str(node) -> str:
    k = node.node_type

    if k == OperatorKind.AND:
        parts = [expr_to_str(c) for c in node.args]
        parts = [p for p in parts if p]
        return " & ".join(parts)

    if k == OperatorKind.NOT:
        inner = node.arg(0)
        return f"~{expr_to_str(inner)}"

    if node.is_fluent_exp():
        return _atom_to_str(node)

    if node.is_true():
        return ""
    if node.is_false():
        return "FALSE"

    raise ValueError(f"Unsupported expression kind for your format: {node}")


def effects_to_str(effects) -> str:
    lits = []
    for eff in effects:
        if eff.is_conditional():
            raise ValueError("Conditional effects (when ...) not supported in this pipeline.")

        atom = _atom_to_str(eff.fluent)

        if eff.value.is_true():
            lits.append(atom)
        elif eff.value.is_false():
            lits.append(f"~{atom}")
        else:
            raise ValueError("Non-boolean effect not supported.")

    return " & ".join(lits)


# --- PDDL -> PlanningProblem ---
def pddl_to_planning_problem(domain_file: str, problem_file: str) -> PlanningProblem:
    reader = PDDLReader()
    up_prob = reader.parse_problem(domain_file, problem_file)

    # 1) Collect which predicate names are DYNAMIC (appear in any effect)
    dynamic_preds = set()
    for act in up_prob.actions:
        for eff in act.effects:
            # eff.fluent is a fluent expression; fluent().name is predicate name
            dynamic_preds.add(eff.fluent.fluent().name)

    # 2) Build a set of TRUE static atoms from the initial state
    static_true = set()
    dynamic_true = set()

    for f, val in up_prob.initial_values.items():
        if not val.is_true():
            continue
        pred = f.fluent().name
        atom = _atom_to_str(f)  # already sanitized/capitalized
        if pred in dynamic_preds:
            dynamic_true.add(atom)
        else:
            static_true.add(atom)

    initial_str = " & ".join(sorted(dynamic_true))

    # 3) Goals: keep them (they should be dynamic in normal problems, but we’ll be safe)
    goal_lits = []
    for g in up_prob.goals:
        s = expr_to_str(g)
        if not s:
            continue
        # If goal mentions static atoms, we can check them now:
        if is_neg_lit(s):
            # goal requires ~StaticAtom; if StaticAtom is true, impossible at any horizon
            if lit_atom(s) in static_true:
                # return a PlanningProblem that will be unsat quickly, or just keep as-is
                # easiest: keep the goal as-is; SATPlan will find UNSAT
                pass
        else:
            # goal requires StaticAtom; if it’s already true statically, drop it
            if s in static_true:
                continue
        goal_lits.append(s)

    goal_str = " & ".join(goal_lits) if goal_lits else ""  # empty goal means trivially satisfied

    # 4) Actions: strip static preconditions that are always true; discard actions impossible due to static facts
    actions = []
    for act in up_prob.actions:
        # preconditions come as list; treat as conjunction of literals
        pre_lits = []
        impossible = False

        for p in act.preconditions:
            s = expr_to_str(p)
            if not s:
                continue

            atom = lit_atom(s)

            # Decide whether this literal is static or dynamic by checking predicate name
            # We can infer static by whether the atom is in static_true/dynamic_true sets only if grounded,
            # but preconditions are schematic. Better: check by predicate name from the FNode directly.
            # So: re-parse predicate name from p if it is a fluent/not fluent.
            def pred_name_of(node):
                if node.is_fluent_exp():
                    return node.fluent().name
                if node.node_type == OperatorKind.NOT and node.arg(0).is_fluent_exp():
                    return node.arg(0).fluent().name
                return None

            pn = pred_name_of(p)

            if pn is not None and pn not in dynamic_preds:
                # STATIC precondition: evaluate using static_true *only if it is ground*.
                # Many static facts in driverlog are ground (Link/Path between locations).
                # If schematic (contains parameters), keep it.
                if "(" in atom and any(ch.islower() for ch in atom.split("(", 1)[1]):
                    # heuristic: if args contain lowercase parameter-like names, keep it
                    pre_lits.append(s)
                else:
                    # ground-ish: we can evaluate
                    if is_neg_lit(s):
                        if atom in static_true:
                            impossible = True
                            break
                        else:
                            # ~StaticAtom and StaticAtom not true -> it holds (assume closed world for statics)
                            continue
                    else:
                        if atom in static_true:
                            continue  # satisfied
                        else:
                            impossible = True
                            break
            else:
                # dynamic precondition
                pre_lits.append(s)

        if impossible:
            continue

        pre = " & ".join(pre_lits)
        eff = effects_to_str(act.effects)

        params = ", ".join(sanitize_ident(p.name) for p in act.parameters)
        act_name = sanitize_ident(act.name)
        signature = f"{act_name}({params})" if params else act_name

        actions.append(Action(signature, precond=pre, effect=eff))

    # Helpful debug counts
    print(f"[PDDL->PlanningProblem] dynamic preds: {len(dynamic_preds)} | init dynamic atoms: {len(dynamic_true)} | init static atoms (dropped): {len(static_true)} | actions kept: {len(actions)}", flush=True)

    return PlanningProblem(initial=initial_str, goals=goal_str, actions=actions)


# --- Run SATPlan ---

def main():
    if len(sys.argv) != 3:
        print("Usage: python3 driver_log_satplan.py <domain.pddl> <problem.pddl>")
        sys.exit(1)

    domain_file, problem_file = sys.argv[1], sys.argv[2]
    problem = pddl_to_planning_problem(domain_file, problem_file)

    working_T = None
    working_plan = None
    print(problem.initial)
    print('\n' + str(problem.goals))
    print('\n' + str(problem.actions))

    for T in range(1, 11):
        print(T)
        plan = SATPlan(problem, solution_length=T, SAT_solver=cdcl_satisfiable)
        if plan:
            working_T = T
            working_plan = plan
            break

    if working_T is None:
        print("No plan found up to horizon 10.")
        return

    print(f"\nFound plan of length {working_T}:")
    for i, a in enumerate(working_plan, 1):
        print(f"{i:2d}. {a}")


if __name__ == "__main__":
    main()
