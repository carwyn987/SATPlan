# BlackBox SATPLAN (Python)

A SAT-based planning system that converts PDDL problems into Boolean satisfiability problems. This is a Python rewrite of the original BlackBox planner by Henry Kautz and Bart Selman.

## Quick Start

```bash
# Clone the repo
git clone <repo-url>
cd SATPLAN/Blackbox/blackbox_python

# Create virtual environment and install dependencies
python3 -m venv .venv
source .venv/bin/activate
pip install python-sat

# Run on the included example (Depot domain)
python blackbox.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl -solver cadical
```

## Requirements

- Python 3.10+
- PySAT: `pip install python-sat`
- Kissat (optional): `pip install passagemath-kissat`
- WalkSAT (optional): build from source (see below)

## Usage

```
python blackbox.py -o <domain.pddl> -f <problem.pddl> [options] [-solver <solver>]
```

**Important:** The `-solver` flag must come last as it consumes all remaining arguments.

### Required Arguments

| Flag | Description |
|------|-------------|
| `-o <file>` | Domain PDDL file |
| `-f <file>` | Problem PDDL file |

## Available Solvers

| Solver | Backend | Incremental | Description |
|--------|---------|:-----------:|-------------|
| **cadical** | PySAT | Yes | CaDiCaL 1.9.5 -- default, top SAT competition performer |
| **glucose** | PySAT | Yes | Glucose 4.2 -- strong on industrial benchmarks |
| **maple** | PySAT | Yes | MapleChrono -- SAT competition 2018 winner |
| **minisat** | PySAT | Yes | MiniSat (GitHub fork) -- classic CDCL solver |
| **dpll** | Built-in Python | No | Pure DPLL with Jeroslow-Wang heuristic (no clause learning) |
| **kissat** | External binary | No | Kissat -- state-of-the-art competition solver |
| **walksat** | External binary | No | WalkSAT -- stochastic local search (incomplete) |
| **graphplan** | Built-in | -- | Backward-chaining search (not SAT-based) |

**Notes:**
- *Incremental* solvers reuse learned clauses across plan horizons. Non-incremental solvers rebuild from scratch at each horizon and are significantly slower on large problems.
- *DPLL* is a pure Python implementation -- useful for educational purposes and small problems but much slower than CDCL solvers on large instances.
- *WalkSAT* is **incomplete**: it can find satisfying assignments but cannot prove unsatisfiability. It returns timeout (not unsat) when it fails to find a solution.

## Running with a Specific Solver

```bash
# Default (CaDiCaL)
python blackbox.py -o domain.pddl -f problem.pddl

# Glucose
python blackbox.py -o domain.pddl -f problem.pddl -solver glucose

# DPLL
python blackbox.py -o domain.pddl -f problem.pddl -solver dpll

# Kissat
python blackbox.py -o domain.pddl -f problem.pddl -solver kissat

# WalkSAT with 10-second timeout per horizon
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 10 walksat
```

## Solver Chaining

Chain solvers with timeouts using `-then`. If the first solver times out, the next one takes over.

```bash
# Try Glucose for 30 seconds, then fall back to CaDiCaL
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 30 glucose -then cadical

# Try GraphPlan first, then CaDiCaL
python blackbox.py -o domain.pddl -f problem.pddl -solver graphplan -then cadical

# Three-stage chain
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 10 maple -then -maxsec 60 glucose -then cadical
```

## Action Minimization

After finding a plan at the minimum makespan, the solver automatically searches for plans with fewer total actions at longer makespans. This uses cardinality constraints (PySAT sequential counter encoding) with fresh solver instances at each candidate makespan.

For example, a Depot problem might find 11 actions at makespan 4 (using 2 trucks in parallel), but then discover a 10-action plan at makespan 6 (using 1 truck sequentially).

## SAT Encoding

The encoder uses several optimizations:

- **AMO ladder encoding**: Mutex cliques are encoded using ladder at-most-one constraints (3(k-1)-1 clauses) instead of pairwise (k(k-1)/2 clauses). Falls back to pairwise in incremental mode.
- **Exists-step semantics**: Two actions are mutex only if ALL orderings fail (not just any). This produces fewer mutex constraints while preserving soundness and completeness.
- **Incremental encoding**: In incremental SAT mode, only newly-added time layers are encoded, avoiding redundant re-encoding of previous layers.

## Building External Solvers

### Kissat

```bash
pip install passagemath-kissat
```

Or build from source:

```bash
git clone https://github.com/arminbiere/kissat.git
cd kissat
./configure && make
cp build/kissat /usr/local/bin/
```

### WalkSAT

```bash
git clone https://gitlab.com/HenryKautz/Walksat.git
cd Walksat/Walksat_v56
make
```

Then place the `walksat` binary either:
- On your PATH (`/usr/local/bin/` or `~/bin/`)
- In the same directory as `blackbox.py`

## Other Options

| Flag | Description |
|------|-------------|
| `-g <file>` | Write plan to output file |
| `-t <int>` | Fixed plan length (0 = auto-increment, default) |
| `-i <level>` | Debug info level: 0 (quiet), 1 (verbose), 2 (detailed) |
| `-n` | Force negative facts |
| `-step <n>` | Graph increment step size (default: 1) |
| `-noskip` | Don't skip graphplan mutex checking |
| `-noopt` | Stop at first solution found |
| `-noincsat` | Disable incremental SAT across horizons |
| `-norelevance` | Disable action/schema relevance pruning |
| `-printlit` | Print WFF literals |
| `-printcnf` | Print DIMACS CNF encoding |
| `-axioms <n>` | SAT encoding preset (see below) |
| `-M <int>` | Max nodes per graph layer (default: 2048) |
| `-maxfail <n>` | Max solver failures before giving up (0 = unlimited) |
| `-maxauto <n>` | Max auto plan length (default: 100) |
| `-maxglobalsec <n>` | Global time limit in seconds |

## SAT Encoding Presets (`-axioms`)

| Value | Name | Axioms Included |
|-------|------|-----------------|
| 7 | default | mutex actions + preconditions + frame axioms |
| 15 | -- | above + mutex facts |
| 31 | compressed | above + action implies effect (prunes some mutexes) |
| 63 | expanded | above + keeps all mutexes |
| 129 | action | mutex actions + action-to-action chaining (no fact propositions) |

## Supported PDDL

Typed STRIPS only:

- `:strips`
- `:typing`
- `:equality`

Does **not** support: conditional effects, disjunctive preconditions, quantified goals, derived predicates, numeric fluents, durative actions, or `:constants`.

## Project Structure

```
blackbox_python/
  blackbox.py        Main entry point and argument parsing
  planner.py         Planning loop, solver dispatch, action minimization
  graphplan.py       Planning graph construction
  graph2wff.py       SAT encoding (CNF generation, AMO ladder encoding)
  sat_interface.py   SAT solver interfaces (PySAT, DPLL, Kissat, WalkSAT)
  utilities.py       Mutex computation (exists-step semantics)
  data_structures.py Core data types (Vertex, Operator, HashTable)
  pddl_parser.py     PDDL domain/problem parser
  justify.py         Plan justification (unnecessary action removal)
  pddl_problems/     Example PDDL files
```
