"""
data_structures.py - Core data types for BlackBox SATPLAN.

Replaces: graphplan.h structs (vertex_t, edgelist_t, op_s, fact_list, etc.)
"""

from dataclasses import dataclass, field
from typing import Optional

# ---------------------------------------------------------------------------
# Constants (from graphplan.h)
# ---------------------------------------------------------------------------
MAXGOALS = 250
HSIZE = 50
MAX_TOKENS = 15
CONNECTOR = '_'
NOOP = "noop"
DELETE = "not"
DEFAULT_MAXNODES = 2 * 1024
MAXMAXNODES = 32 * 1024
NUMINTS = MAXMAXNODES // 32

# Return / status codes
SAME = 0
DIFFERENT = -1
OK = 1
YES = 1
NO = 0
NEW_INSTS = 2

# SAT solver return values
Unsat = 0
Sat = 1
Timeout = 2
Failure = 3
Simplified = 4

# Solver type identifiers
Anysat = 0
Graphplan_Solver = 1
Compact_Solver = 2

# Print masks
PrintLit = 1
PrintCNF = 2
PrintExit = 4
PrintMap = 8
PrintModel = 16

# Axiom output flags
BB_OutputOpMutex = 1
BB_OutputOpPre = 2
BB_OutputFactFrame = 4
BB_OutputFactMutex = 8
BB_OutputOpEffect = 16
BB_OutputRedundant = 32
BB_OutputSymmetric = 64
BB_OutputOpPreOp = 128
BB_OutputActDefs = 256

# Solver rate constants (iterations per check)
Graphplan_Rate = 100
Satz_Rate = 20
Walksat_Rate = 500

# ---------------------------------------------------------------------------
# Helper predicates
# ---------------------------------------------------------------------------

def is_var(name: str) -> bool:
    """Check if a token is a variable (starts with '?')."""
    return len(name) > 0 and name[0] == '?'


def is_const(name: str) -> bool:
    """Check if a token is a constant (does not start with '?')."""
    return len(name) > 0 and name[0] != '?'


# ---------------------------------------------------------------------------
# Vertex - planning graph node (fact or operator)
# ---------------------------------------------------------------------------

class Vertex:
    """A node in the planning graph.  Can represent a fact or an operator/noop."""

    __slots__ = (
        'name', 'is_noop', 'in_edges', 'out_edges', 'del_list', 'del_edges',
        'exclusive', 'exclusive_set', 'excl_in_this_step', 'excl_in_this_step_set',
        'used', 'is_true', 'cant_do', 'needed',
        'uid_block', 'uid_mask', 'uid_index',
        'prev_time', 'next_time',
        'rand1', 'junk', 'prop',
        'next_vertex', 'hashval',
    )

    def __init__(self, name: str = ""):
        self.name: str = name
        self.is_noop: int = 0

        # Edges (lists of Vertex references)
        self.in_edges: list['Vertex'] = []
        self.out_edges: list['Vertex'] = []
        self.del_list: list[str] = []          # names of delete-effects
        self.del_edges: list['Vertex'] = []    # pointers to deleted-fact vertices

        # Mutual exclusion
        self.exclusive: list['Vertex'] = []    # linked-list replacement
        self.exclusive_set: set[int] = set()   # fast O(1) check via uid_index
        self.excl_in_this_step: list['Vertex'] = []
        self.excl_in_this_step_set: set[int] = set()

        # Search flags
        self.used: int = 0          # 1+index if used in plan (avoid zero)
        self.is_true: int = 0       # marked true in initial state
        self.cant_do: int = 0       # counter for exclusive marking
        self.needed: int = 0        # needed in SAT encoding

        # Unique ID for bit-vector operations
        self.uid_block: int = 0
        self.uid_mask: int = 0
        self.uid_index: int = -1    # sequential id for set-based exclusion

        # Temporal links
        self.prev_time: Optional['Vertex'] = None
        self.next_time: Optional['Vertex'] = None

        # Misc
        self.rand1: int = 0
        self.junk: int = 0          # general purpose (NECESSARY/PRUNED/ADDED in justify)
        self.prop: int = 0          # propositional variable number in SAT encoding

        # Hash chain pointer (for hash table buckets)
        self.next_vertex: Optional['Vertex'] = None
        self.hashval: int = 0

    def __repr__(self):
        return f"Vertex({self.name!r})"


# ---------------------------------------------------------------------------
# Operator - an action schema (uninstantiated)
# ---------------------------------------------------------------------------

@dataclass
class Operator:
    """An action schema with parameters, preconditions, and effects."""
    name: str = ""
    params: list = field(default_factory=list)       # list of fact-lists (typed params)
    preconds: list = field(default_factory=list)      # list of fact-lists
    effects: list = field(default_factory=list)       # list of fact-lists


# ---------------------------------------------------------------------------
# Hash table (chaining)
# ---------------------------------------------------------------------------

class HashTable:
    """Simple chaining hash table mapping string keys to Vertex objects.

    Replaces ``hashtable_t[HSIZE]`` from the C code.  Uses Python dict
    internally for speed but provides the same iterator interface.
    """

    def __init__(self):
        self._dict: dict[str, Vertex] = {}

    # --- core operations ---------------------------------------------------

    def lookup(self, name: str) -> Optional[Vertex]:
        return self._dict.get(name)

    def insert(self, name: str, vertex: Optional[Vertex] = None) -> Vertex:
        """Insert or retrieve a vertex.  If *vertex* is ``None`` a fresh one
        is created.  Returns the vertex now associated with *name*."""
        if name in self._dict:
            return self._dict[name]
        if vertex is None:
            vertex = Vertex(name)
        else:
            vertex.name = name
        self._dict[name] = vertex
        return vertex

    def __contains__(self, name: str) -> bool:
        return name in self._dict

    def __len__(self) -> int:
        return len(self._dict)

    def __iter__(self):
        return iter(self._dict.values())

    def values(self):
        return self._dict.values()

    def items(self):
        return self._dict.items()

    def get(self, name: str, default=None):
        return self._dict.get(name, default)


# ---------------------------------------------------------------------------
# Solver specification
# ---------------------------------------------------------------------------

@dataclass
class SolverSpec:
    """Mirrors ``bb_solver_spec`` from interface.h."""
    solver_name: str = "graphplan"     # "graphplan", "cadical", "glucose", "maple"
    solver_type: int = Graphplan_Solver  # Graphplan_Solver / Anysat
    maxsec: int = 0
    maxit: int = 0
    argv: list = field(default_factory=list)

    @property
    def rate(self) -> int:
        return 100
