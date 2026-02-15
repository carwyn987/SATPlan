"""
sat_interface.py - Interface to SAT solvers via PySAT.

Replaces: sat_solver.cpp

Uses the python-sat (PySAT) library for SAT solving. No C++ compilation
or external binaries required.

Available solvers:
  - cadical  (CaDiCaL 1.9.5) - default, top SAT competition performer
  - glucose  (Glucose 4.2)   - strong on industrial benchmarks
  - maple   (MapleChrono)    - SAT competition 2018 winner

Install: pip install python-sat
"""

from __future__ import annotations
import sys
import time
from typing import Optional

from pysat.solvers import Cadical195, Glucose42, MapleChrono

from data_structures import Sat, Unsat, Timeout, Failure


# ── Solver dispatch ──────────────────────────────────────────────────────────

SOLVER_CLASSES = {
    'cadical': Cadical195,
    'cd195': Cadical195,
    'glucose': Glucose42,
    'g42': Glucose42,
    'maple': MapleChrono,
    'mcb': MapleChrono,
}

DEFAULT_SOLVER = 'cadical'


class IncrementalSATSolver:
    """Stateful incremental SAT session backed by a PySAT solver instance."""

    def __init__(self, solver_name: str = DEFAULT_SOLVER, debug: int = 0):
        key = (solver_name or DEFAULT_SOLVER).lower()
        solver_cls = SOLVER_CLASSES.get(key)
        if solver_cls is None:
            raise ValueError(f"Unknown solver '{solver_name}'")
        self.solver_name = key
        self.solver_cls = solver_cls
        self.debug = debug
        self.solver = solver_cls()

    def reset(self):
        """Drop all clauses and recreate the underlying SAT solver."""
        self.delete()
        self.solver = self.solver_cls()

    def add_clauses(self, clauses: list[list[int]]):
        for clause in clauses:
            self.solver.add_clause(clause)

    def solve(self, numvar: int, maxtime: int = 0,
              assumptions: Optional[list[int]] = None) -> tuple[int, list[int]]:
        """Solve with optional assumptions and return (status, 1-indexed model)."""
        assumps = assumptions if assumptions is not None else []
        soln = [0] * (numvar + 1)
        try:
            before = self.solver.accum_stats().copy() if hasattr(self.solver, 'accum_stats') else None
            if maxtime > 0:
                try:
                    result = self.solver.solve_limited(expect_interrupt=True,
                                                      timer=maxtime,
                                                      assumptions=assumps)
                except TypeError:
                    # Some wrappers do not accept timer/assumptions in solve_limited.
                    try:
                        result = self.solver.solve_limited(expect_interrupt=True,
                                                          assumptions=assumps)
                    except TypeError:
                        result = self.solver.solve_limited(expect_interrupt=True)
            else:
                result = self.solver.solve(assumptions=assumps)

            if result is True:
                model = self.solver.get_model()
                if model:
                    for lit in model:
                        var = abs(lit)
                        if 1 <= var <= numvar:
                            soln[var] = 1 if lit > 0 else 0
                if self.debug >= 1 and before is not None:
                    after = self.solver.accum_stats().copy()
                    delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                             for k in after.keys()}
                    print("  SAT search: "
                          f"decisions={delta.get('decisions', 0)} "
                          f"conflicts={delta.get('conflicts', 0)} "
                          f"propagations={delta.get('propagations', 0)}")
                return Sat, soln
            if result is False:
                if self.debug >= 1 and before is not None:
                    after = self.solver.accum_stats().copy()
                    delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                             for k in after.keys()}
                    print("  SAT search: "
                          f"decisions={delta.get('decisions', 0)} "
                          f"conflicts={delta.get('conflicts', 0)} "
                          f"propagations={delta.get('propagations', 0)}")
                return Unsat, soln
            if self.debug >= 1 and before is not None:
                after = self.solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            return Timeout, soln
        except Exception as e:
            print(f"  SAT solver error: {e}", file=sys.stderr)
            return Failure, soln

    def delete(self):
        if self.solver is not None:
            try:
                self.solver.delete()
            finally:
                self.solver = None


def _solve_with_pysat(solver_cls, clauses: list[list[int]], numvar: int,
                      numclause: int, maxtime: int = 0,
                      debug: int = 0) -> tuple[int, list[int]]:
    """Run a PySAT solver on the given CNF clauses.

    Returns (status, soln) where soln is a 1-indexed assignment array:
    soln[v] = 1 if variable v is true, 0 if false.
    """
    soln = [0] * (numvar + 1)

    try:
        solver = solver_cls()
        for clause in clauses:
            solver.add_clause(clause)
        before = solver.accum_stats().copy() if hasattr(solver, 'accum_stats') else None

        if maxtime > 0:
            result = solver.solve_limited(expect_interrupt=True,
                                          timer=maxtime)
        else:
            result = solver.solve()

        if result is True:
            model = solver.get_model()
            if model:
                for lit in model:
                    var = abs(lit)
                    if 1 <= var <= numvar:
                        soln[var] = 1 if lit > 0 else 0
            if debug >= 1 and before is not None:
                after = solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            solver.delete()
            return Sat, soln
        elif result is False:
            if debug >= 1 and before is not None:
                after = solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            solver.delete()
            return Unsat, soln
        else:
            if debug >= 1 and before is not None:
                after = solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            solver.delete()
            return Timeout, soln

    except Exception as e:
        print(f"  SAT solver error: {e}", file=sys.stderr)
        return Failure, soln


# ── Public API (matches original interface used by planner.py) ───────────────

def bb_satsolve_cadical(clauses: list[list[int]], numvar: int, numclause: int,
                        maxtime: int = 0, extra_args: list[str] | None = None,
                        debug: int = 0) -> tuple[int, list[int]]:
    """Solve with CaDiCaL 1.9.5."""
    if debug >= 2:
        print(f"  [cadical] {numvar} vars, {numclause} clauses")
    return _solve_with_pysat(Cadical195, clauses, numvar, numclause,
                             maxtime, debug)


def bb_satsolve_glucose(clauses: list[list[int]], numvar: int, numclause: int,
                        maxtime: int = 0, extra_args: list[str] | None = None,
                        debug: int = 0) -> tuple[int, list[int]]:
    """Solve with Glucose 4.2."""
    if debug >= 2:
        print(f"  [glucose] {numvar} vars, {numclause} clauses")
    return _solve_with_pysat(Glucose42, clauses, numvar, numclause,
                             maxtime, debug)


def bb_satsolve_maple(clauses: list[list[int]], numvar: int, numclause: int,
                      maxtime: int = 0, extra_args: list[str] | None = None,
                      debug: int = 0) -> tuple[int, list[int]]:
    """Solve with MapleChrono (MapleLCMDistChronoBT)."""
    if debug >= 2:
        print(f"  [maple] {numvar} vars, {numclause} clauses")
    return _solve_with_pysat(MapleChrono, clauses, numvar, numclause,
                             maxtime, debug)
