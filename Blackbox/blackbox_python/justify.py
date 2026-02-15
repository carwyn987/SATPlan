"""
justify.py - Plan justification (remove unnecessary actions).

Replaces: justify.cpp

After a plan is extracted, greedily removes actions whose effects are
not needed, cascading deletions forward through time.
"""

from __future__ import annotations
from typing import Optional

from data_structures import Vertex, HashTable, CONNECTOR
from graphplan import PlanningGraph

# Justification markers (stored in vertex.junk)
NECESSARY = 1
PRUNED = 2
ADDED = 3


def justify_plan(graph: PlanningGraph, maxtime: int) -> int:
    """Remove unnecessary actions from the plan.

    Returns the number of pruned actions.
    """
    num_pruned = 0

    # 1. Mark goal-supporting facts as necessary
    _mark_goals_as_necessary(graph, maxtime)

    # 2. Try to remove each non-NOOP used action
    for t in range(maxtime):
        for op in graph.op_table[t]:
            if op.used and not op.is_noop:
                removed = _justify_action(graph, op, t, maxtime)
                if removed:
                    num_pruned += removed

    if num_pruned > 0:
        print(f"  Justify: removed {num_pruned} unnecessary actions")

    return num_pruned


def _mark_goals_as_necessary(graph: PlanningGraph, maxtime: int):
    """Mark facts that directly serve goals as NECESSARY.

    Walk backward from goal facts along NOOP chains, marking each
    fact as NECESSARY if its supporting NOOP is used.
    """
    for g in graph.the_goals:
        name = CONNECTOR.join(g)
        fv = graph.fact_table[maxtime].lookup(name)
        if fv is None:
            continue
        fv.junk = NECESSARY

        # Walk backward through NOOP chain
        cur = fv
        while cur and cur.prev_time:
            prev = cur.prev_time
            # Check if there's a used NOOP connecting prev to cur
            noop_found = False
            for op in cur.in_edges:
                if op.is_noop and op.used:
                    noop_found = True
                    break
            if noop_found:
                prev.junk = NECESSARY
                cur = prev
            else:
                break


def _justify_action(graph: PlanningGraph, act: Vertex, st_time: int,
                    maxtime: int) -> int:
    """Attempt to remove *act* and cascade.

    Returns the number of actions pruned, or 0 if removal failed.
    """
    # Track changes for rollback
    pruned_ops: list[list[Vertex]] = [[] for _ in range(maxtime)]
    changed_facts: list[list[Vertex]] = [[] for _ in range(maxtime + 1)]
    total_pruned = 0

    # Mark starting action for removal
    pruned_ops[st_time].append(act)
    total_pruned += 1

    failed = False
    for t in range(st_time, maxtime):
        for op in pruned_ops[t]:
            ok = _remove_action(graph, op, t, pruned_ops, changed_facts,
                                maxtime)
            if not ok:
                failed = True
                break
        if failed:
            break

    if failed:
        _restore_all(pruned_ops, changed_facts, maxtime)
        return 0

    return total_pruned


def _remove_action(graph: PlanningGraph, act: Vertex, t: int,
                   pruned_ops: list[list[Vertex]],
                   changed_facts: list[list[Vertex]],
                   maxtime: int) -> bool:
    """Remove a single action and propagate effects.

    Returns True if removal succeeded, False if it would violate a
    NECESSARY fact.
    """
    # Check each output fact
    for eff_fact in act.out_edges:
        if eff_fact.junk == ADDED:
            continue  # was added by a previous removal in this round

        if eff_fact.junk == NECESSARY:
            # Check if another used action also produces this fact
            has_backup = False
            for other_op in eff_fact.in_edges:
                if other_op is not act and other_op.used:
                    has_backup = True
                    break
            if not has_backup:
                return False  # can't remove: would break a necessary fact

        # Check if another action still produces this fact
        has_other_producer = False
        for other_op in eff_fact.in_edges:
            if other_op is not act and other_op.used:
                has_other_producer = True
                break

        if not has_other_producer:
            # This fact will become false
            eff_fact.junk = PRUNED
            eff_fact.is_true = 0
            changed_facts[t + 1].append(eff_fact) if t + 1 <= maxtime else None

            # Cascade: any action that uses this fact must also be removed
            for consumer in eff_fact.out_edges:
                if consumer.used and consumer not in pruned_ops[t + 1] and t + 1 < maxtime:
                    pruned_ops[t + 1].append(consumer)

    # Remove the action
    act.used = 0

    # Handle delete effects: facts that were deleted now become "added" back
    for del_fact in act.del_edges:
        if del_fact.junk == PRUNED:
            continue
        del_fact.junk = ADDED
        del_fact.is_true = 1
        changed_facts[t + 1].append(del_fact) if t + 1 <= maxtime else None

    return True


def _restore_all(pruned_ops: list[list[Vertex]],
                 changed_facts: list[list[Vertex]],
                 maxtime: int):
    """Restore all changes from a failed justification attempt."""
    for t in range(maxtime):
        for op in pruned_ops[t]:
            op.used = 1

    for t in range(maxtime + 1):
        for fv in changed_facts[t]:
            if fv.junk == PRUNED:
                fv.is_true = 1
            elif fv.junk == ADDED:
                fv.is_true = 0
            fv.junk = 0
