from planning import PlanningProblem, Action, SATPlan
from logic import cdcl_satisfiable, to_cnf, conjuncts

def blocks_world_problem():
    return PlanningProblem(
        initial='On(A, B) & Clear(A) & OnTable(B) & OnTable(C) & Clear(C)',
        goals='On(B, A) & On(C, B)',
        actions=[
            Action('ToTable(x, y)',
                   precond='On(x, y) & Clear(x)',
                   effect='~On(x, y) & Clear(y) & OnTable(x)'),
            Action('FromTable(y, x)',
                   precond='OnTable(y) & Clear(y) & Clear(x)',
                   effect='~OnTable(y) & ~Clear(x) & On(y, x)')
        ]
    )



def main():
    problem = blocks_world_problem()

    working_T = None
    working_plan = None
    for T in range(0, 11):
        plan = SATPlan(problem, solution_length=T, SAT_solver=cdcl_satisfiable)
        if plan:
            working_T = T
            working_plan = plan
            print(plan)
            break

    if working_T is None:
        print("No plan found up to horizon 10.")
        return


    print(f"\nFound plan of length {working_T}:")
    for i, a in enumerate(working_plan, 1):
        print(f"{i:2d}. {a}")

if __name__ == "__main__":
    main()
