#!/usr/bin/env python3
"""
run_sat_experiments.py

Run Blackbox/SATPlan clause-count experiments across multiple PDDL test suites,
parse the printed horizon statistics, and plot trends (e.g., mutex clauses and
plan action counts vs. horizon).

Expected directory layout:
  pddl/
    <suite_name>/
      domain.pddl
      problem*.pddl
    <suite_name>/
      domain.pddl
      problem*.pddl
    ...

Example:
  python run_sat_experiments.py --root pddl
"""

from __future__ import annotations

import argparse
import glob
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional

import matplotlib.pyplot as plt


ParsedSeries = Tuple[List[int], List[int]]
GroupedSeries = Dict[str, List[ParsedSeries]]


def parse_blackbox_log(path: str) -> Dict[str, List[int]]:
    """
    Parse a count_clauses.py stdout log into per-horizon numeric series.

    Returns a dict of lists with keys:
      t, vars, total, init, goal, precond, frame, mutex, actions

    Notes:
      - Numbers may include commas (e.g., 1,061).
      - A horizon block is considered complete when the '<N> actions' line is seen.
    """
    data: Dict[str, List[int]] = {
        "t": [],
        "vars": [],
        "total": [],
        "init": [],
        "goal": [],
        "precond": [],
        "frame": [],
        "mutex": [],
        "actions": [],
    }

    patterns = {
        "t": re.compile(r"Horizon t:\s*(\d+)"),
        "vars": re.compile(r"Vars:\s*([\d,]+)"),
        "total": re.compile(r"Total Clauses:\s*([\d,]+)"),
        "init": re.compile(r"Init:\s*([\d,]+)"),
        "goal": re.compile(r"Goal:\s*([\d,]+)"),
        "precond": re.compile(r"Precond:\s*([\d,]+)"),
        "frame": re.compile(r"Frame:\s*([\d,]+)"),
        "mutex": re.compile(r"Mutex AMO:\s*([\d,]+)"),
        "actions": re.compile(r"(\d+)\s+actions"),
    }

    def to_int(s: str) -> int:
        return int(s.replace(",", ""))

    current: Dict[str, int] = {}

    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.strip()

            m = patterns["t"].search(line)
            if m:
                current = {"t": int(m.group(1))}
                continue

            for key in ("vars", "total", "init", "goal", "precond", "frame", "mutex"):
                m = patterns[key].search(line)
                if m:
                    current[key] = to_int(m.group(1))
                    break
            else:
                m = patterns["actions"].search(line)
                if m and current:
                    current["actions"] = int(m.group(1))

                    required = list(data.keys())
                    missing = [k for k in required if k not in current]
                    if missing:
                        raise ValueError(f"Malformed horizon block (missing {missing}): {current}")

                    for k in required:
                        data[k].append(current[k])

                    current = {}

    return data


@dataclass(frozen=True)
class ExperimentCase:
    suite: str
    domain_pddl: str
    problem_pddl: str


def run_count_clauses(
    count_clauses_py: str,
    domain_pddl: str,
    problem_pddl: str,
    maxtime: int,
    axioms: int,
    solver: str,
) -> str:
    """Run count_clauses.py and return stdout text (raises on nonzero exit)."""
    cmd = [
        "python",
        count_clauses_py,
        "-o", domain_pddl,
        "-f", problem_pddl,
        "-maxtime", str(maxtime),
        "-axioms", str(axioms),
        "-solver", solver,
    ]
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(
            "count_clauses.py failed\n"
            f"cmd: {' '.join(cmd)}\n\n"
            f"stdout:\n{res.stdout}\n\n"
            f"stderr:\n{res.stderr}\n"
        )
    return res.stdout


def discover_cases(root: str, pattern: str = "problem*.pddl") -> List[ExperimentCase]:
    """Discover (domain, problem) pairs under ROOT/<suite>/."""
    cases: List[ExperimentCase] = []
    for suite_dir in sorted(glob.glob(os.path.join(root, "*"))):
        if not os.path.isdir(suite_dir):
            continue

        domain_pddl = os.path.join(suite_dir, "domain.pddl")
        if not os.path.exists(domain_pddl):
            continue

        suite = os.path.basename(suite_dir)
        for prob in sorted(glob.glob(os.path.join(suite_dir, pattern))):
            cases.append(ExperimentCase(suite=suite, domain_pddl=domain_pddl, problem_pddl=prob))

    return cases


def plot_grouped_series(
    grouped: GroupedSeries,
    title: str,
    ylabel: str,
    outpath: Optional[str],
) -> None:
    """Plot one or more (t,y) series per label; save to outpath if provided."""
    plt.figure()

    for label, runs in grouped.items():
        for t, y in runs:
            plt.plot(t, y, marker="o", label=label)

    plt.xlabel("Horizon t")
    plt.ylabel(ylabel)
    plt.title(title)

    handles, labels = plt.gca().get_legend_handles_labels()
    seen = set()
    uniq_handles, uniq_labels = [], []
    for h, l in zip(handles, labels):
        if l not in seen:
            seen.add(l)
            uniq_handles.append(h)
            uniq_labels.append(l)
    plt.legend(uniq_handles, uniq_labels, loc="best")

    plt.tight_layout()
    if outpath:
        plt.savefig(outpath, dpi=200)
    plt.show()


def main() -> None:
    ap = argparse.ArgumentParser(description="Run SATPlan clause-count experiments and plot trends.")
    ap.add_argument("--root", required=True, help="Root folder containing suite subfolders.")
    ap.add_argument("--count_clauses", default="Blackbox/blackbox_python/count_clauses.py")
    ap.add_argument("--problem_glob", default="problem*.pddl", help="Problem filename glob within each suite.")
    ap.add_argument("--maxtime", type=int, default=10)
    ap.add_argument("--axioms", type=int, default=7)
    ap.add_argument("--solver", default="cadical")
    ap.add_argument("--outdir", default="plots")
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)

    cases = discover_cases(args.root, pattern=args.problem_glob)
    if not cases:
        raise SystemExit(
            f"No cases found under {args.root}. "
            f"Expected {args.root}/<suite>/domain.pddl and {args.problem_glob}."
        )

    mutex_by_suite: GroupedSeries = {}
    actions_by_suite: GroupedSeries = {}

    for case in cases:
        stdout = run_count_clauses(
            args.count_clauses,
            case.domain_pddl,
            case.problem_pddl,
            maxtime=args.maxtime,
            axioms=args.axioms,
            solver=args.solver,
        )
        print(stdout)

        with tempfile.NamedTemporaryFile(mode="w+", suffix=".log", delete=True) as tmp:
            tmp.write(stdout)
            tmp.flush()
            parsed = parse_blackbox_log(tmp.name)

        t = parsed["t"]
        mutex = parsed["mutex"]
        actions = parsed["actions"]

        mutex_by_suite.setdefault(case.suite, []).append((t, mutex))
        actions_by_suite.setdefault(case.suite, []).append((t, actions))

        prob_base = os.path.splitext(os.path.basename(case.problem_pddl))[0]
        print(f"[OK] {case.suite}/{prob_base}: horizons={t[0] if t else 'none'}..{t[-1] if t else 'none'}")

    plot_grouped_series(
        mutex_by_suite,
        title="Mutex AMO Clauses vs Horizon (by suite)",
        ylabel="Mutex AMO clauses",
        outpath=os.path.join(args.outdir, "mutex_by_suite.png"),
    )

    plot_grouped_series(
        actions_by_suite,
        title="# Actions in Plan vs Horizon (by suite)",
        ylabel="# actions",
        outpath=os.path.join(args.outdir, "actions_by_suite.png"),
    )


if __name__ == "__main__":
    main()