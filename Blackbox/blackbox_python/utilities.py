"""
utilities.py - Mutex computation, string / hash utilities.

Replaces: utilities.cpp + hash.cpp
"""

from __future__ import annotations
import random
from typing import Optional

from data_structures import (
    Vertex, HashTable, CONNECTOR, NOOP, DELETE, YES, NO, NEW_INSTS,
    is_var, is_const,
)


# ── String / token utilities ──────────────────────────────────────────────────

def make_noop_string(s: str) -> str:
    """Prepend 'noop_' to a fact name."""
    return NOOP + CONNECTOR + s


def token_list_from_string(s: str) -> list[str]:
    """Split a connector-joined name into tokens.

    Example: ``"move_a_b"`` → ``['move', 'a', 'b']``
    """
    return s.split(CONNECTOR)


def instantiate_into_string(tokens: list[str],
                            insts: dict[str, str],
                            fail_ok: bool = False) -> Optional[str]:
    """Substitute variables in *tokens* using *insts* and join with CONNECTOR.

    Returns ``None`` if a variable has no binding and *fail_ok* is ``True``.
    Raises ``KeyError`` otherwise.
    """
    parts: list[str] = []
    for t in tokens:
        if is_var(t):
            val = insts.get(t)
            if val is None:
                if fail_ok:
                    return None
                raise KeyError(f"Unbound variable {t}")
            parts.append(val)
        else:
            parts.append(t)
    return CONNECTOR.join(parts)


def make_op_string(op_name: str, insts: dict[str, str],
                   params: list[str]) -> str:
    """Build the ground operator name: ``op_c1_c2_...``."""
    parts: list[str] = [op_name]
    for p in params:
        if is_var(p):
            parts.append(insts.get(p, p))
        else:
            parts.append(p)
    return CONNECTOR.join(parts)


def compare_and_instantiate(
    pattern: list[str],
    fact: list[str],
    insts: dict[str, str],
) -> int:
    """Unify *pattern* with *fact* under current instantiation *insts*.

    Returns
    -------
    YES (1)
        Exact match, no new bindings.
    NEW_INSTS (2)
        Match with new variable bindings added to *insts*.
    NO (0)
        No match.

    On ``NO``, any tentative bindings added during this call are removed.
    """
    if len(pattern) != len(fact):
        return NO

    new_bindings: list[str] = []   # variables bound during this call
    result = YES

    for p_tok, f_tok in zip(pattern, fact):
        if is_const(p_tok):
            if p_tok != f_tok:
                # rollback
                for v in new_bindings:
                    del insts[v]
                return NO
        else:
            # p_tok is a variable
            bound = insts.get(p_tok)
            if bound is not None:
                if bound != f_tok:
                    for v in new_bindings:
                        del insts[v]
                    return NO
            else:
                insts[p_tok] = f_tok
                new_bindings.append(p_tok)
                result = NEW_INSTS

    return result


def undo_instantiations(insts: dict[str, str], keys: list[str]):
    """Remove *keys* from *insts* (backtracking helper)."""
    for k in keys:
        insts.pop(k, None)


# ── Mutex computation ─────────────────────────────────────────────────────────

def are_mutex(v1: Vertex, v2: Vertex) -> bool:
    """O(1) check whether two vertices are mutually exclusive."""
    return v2.uid_index in v1.exclusive_set


def do_exclusive(v1: Vertex, v2: Vertex):
    """Mark *v1* and *v2* mutually exclusive (bi-directional)."""
    if v1 is v2:
        return
    if v2.uid_index in v1.exclusive_set:
        return  # already marked
    v1.exclusive_set.add(v2.uid_index)
    v2.exclusive_set.add(v1.uid_index)
    v1.exclusive.append(v2)
    v2.exclusive.append(v1)


def do_exclusive_this_step(v1: Vertex, v2: Vertex):
    """Mark *v1* and *v2* as exclusively in this step (for lower-bound)."""
    if v1 is v2:
        return
    if v2.uid_index in v1.excl_in_this_step_set:
        return
    v1.excl_in_this_step_set.add(v2.uid_index)
    v2.excl_in_this_step_set.add(v1.uid_index)
    v1.excl_in_this_step.append(v2)
    v2.excl_in_this_step.append(v1)


def find_all_mutex_ops(op_table: HashTable, fact_table_cur: HashTable,
                       fact_table_next: HashTable, time: int):
    """Compute all operator mutexes at time step *time*.

    Three types of mutex:
      1. Conflicting preconditions (preconditions are mutex)
      2. Delete conflicts (deletes precondition/effect of other)
      3. NOOP conflicts
    """
    for v in op_table:
        _find_mutex_ops_single(v, op_table, fact_table_cur, fact_table_next, time)


def _find_mutex_ops_single(v: Vertex, op_table: HashTable,
                           fact_table_cur: HashTable,
                           fact_table_next: HashTable, time: int):
    """Find mutexes for a single operator *v*."""

    # --- Type 1: conflicting preconditions --------------------------------
    for prec_fact in v.in_edges:
        for mutex_fact in prec_fact.exclusive:
            # All operators that need mutex_fact are mutex with v
            for other_op in mutex_fact.out_edges:
                if other_op is not v and other_op.uid_index >= 0:
                    do_exclusive(v, other_op)

    # --- Type 2: delete conflicts -----------------------------------------
    for del_name in v.del_list:
        # Find the fact in the next layer that this op deletes
        fact_next = fact_table_next.lookup(del_name)
        if fact_next is None:
            continue
        fact_cur = fact_next.prev_time
        if fact_cur is None:
            continue
        # All ops requiring or producing this fact are mutex with v
        for other_op in fact_cur.out_edges:
            if other_op is not v and other_op.uid_index >= 0:
                do_exclusive(v, other_op)
        # All ops that produce the next-layer fact
        for other_op in fact_next.in_edges:
            if other_op is not v and other_op.uid_index >= 0:
                do_exclusive(v, other_op)

    # --- Type 3: NOOP conflicts -------------------------------------------
    if v.is_noop:
        # NOOP for fact f: mutex with all non-noop producers of f
        if v.out_edges:
            fact_next = v.out_edges[0]  # noop has exactly one output
            for other_op in fact_next.in_edges:
                if other_op is not v and not other_op.is_noop:
                    do_exclusive(v, other_op)


def find_mutex_facts(fact_table: HashTable) -> tuple[int, int]:
    """Mark facts mutex if ALL their producer-pairs are pairwise mutex.

    Returns ``(fact_count, exclusive_pair_count)``.
    """
    facts = list(fact_table)
    fact_set = set(facts)
    fcount = len(facts)
    ecount = 0

    for i, fi in enumerate(facts):
        # New facts: check broadly against all facts (except duplicate checks).
        if fi.prev_time is None:
            for j, fj in enumerate(facts):
                if fj.prev_time is None and j <= i:
                    continue
                if _are_facts_exclusive(fi, fj):
                    do_exclusive(fi, fj)
                    ecount += 1
        else:
            # Old facts: only re-check successors of previous-layer exclusives.
            for prev_excl in fi.prev_time.exclusive:
                fj = prev_excl.next_time
                if fj is None or fj not in fact_set:
                    continue
                if id(fj) < id(fi):
                    continue
                if _are_facts_exclusive(fi, fj):
                    do_exclusive(fi, fj)
                    ecount += 1

    return fcount, ecount


def _are_facts_exclusive(f1: Vertex, f2: Vertex) -> bool:
    """Two facts are mutex if every pair of their producers is mutex."""
    producers1 = f1.in_edges
    producers2 = f2.in_edges
    if not producers1 or not producers2:
        return False
    for p1 in producers1:
        for p2 in producers2:
            if p1 is p2:
                return False
            if not are_mutex(p1, p2):
                return False
    return True


# ── Memoisation (bad-set cache for backward search) ──────────────────────────

class SetTable:
    """Bit-vector based set memoisation table (replaces bad_table/good_table).

    Uses frozenset of vertex uid_index values as keys for fast lookup.
    """

    def __init__(self):
        self._store: dict[tuple[int, int, frozenset[int]], bool] = {}
        self.inserts = 0
        self.hits = 0

    def lookup(self, goals: list[Vertex], time: int) -> bool:
        """Return ``True`` if this goal set at *time* is in the table."""
        key = self._make_key(goals, time)
        if key in self._store:
            self.hits += 1
            return True
        return False

    def insert(self, goals: list[Vertex], time: int):
        key = self._make_key(goals, time)
        self._store[key] = True
        self.inserts += 1

    def subset_lookup(self, goals: list[Vertex], time: int) -> bool:
        """Check if removing any single goal yields a known-bad set."""
        for i in range(len(goals)):
            sub = goals[:i] + goals[i+1:]
            if self.lookup(sub, time):
                return True
        return False

    @staticmethod
    def _make_key(goals: list[Vertex], time: int) -> tuple:
        s = sum(v.rand1 for v in goals)
        fs = frozenset(v.uid_index for v in goals)
        return (time, s, fs)


# ── Lower-bound heuristic (clique detection) ────────────────────────────────

def can_hope_to_solve(goals: list[Vertex], time: int) -> bool:
    """Greedy clique lower-bound: if the maximum clique among mutually
    exclusive goals exceeds *time*, the goal set cannot be solved."""
    if time <= 0 or len(goals) <= 1:
        return True

    n = len(goals)
    # Build adjacency: which goals are exclusive with each other?
    adj: list[set[int]] = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if goals[j].uid_index in goals[i].excl_in_this_step_set:
                adj[i].add(j)
                adj[j].add(i)

    # Greedy clique: always pick vertex with highest degree in remaining graph
    remaining = set(range(n))
    clique_size = 0
    while remaining:
        best = max(remaining, key=lambda x: len(adj[x] & remaining))
        if len(adj[best] & remaining) == 0 and clique_size > 0:
            break
        clique_size += 1
        neighbours = adj[best] & remaining
        remaining = neighbours  # keep only neighbours for next iteration

    return clique_size <= time


# ── Luby sequence (for restart strategies) ────────────────────────────────────

def luby_super(i: int) -> int:
    """Compute the *i*-th element of the Luby sequence."""
    k = 1
    while True:
        if i == (1 << k) - 1:
            return 1 << (k - 1)
        if (1 << (k - 1)) <= i < (1 << k) - 1:
            return luby_super(i - (1 << (k - 1)) + 1)
        k += 1


# ── Miscellaneous ────────────────────────────────────────────────────────────

def hash_name(name: str, size: int = 50) -> int:
    """Simple hash for vertex names (matches C version)."""
    h = 0
    for ch in name:
        h = (h * 31 + ord(ch)) & 0xFFFFFFFF
    return h % size
