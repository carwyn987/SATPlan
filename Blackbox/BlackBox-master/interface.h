/*******************************************************************************/
/*       Following are used to connect planner/solver                          */
/*******************************************************************************/

#define FALSE 0
#define TRUE 1

/* Tracing messages go to STDMSG */
#define STDMSG stdout
/* wffs, solutions, models go to STDDATA */
#define STDDATA stdout

/* Front-end invokes bb_satsolve to run the solver.
   Solver calls bb_limitp to determine if its time is up --
   should call it once per iteration (backtrack or flip). */

int bb_limitp(int rate);  /* returns 1 if time limit reached, 0 otherwise */

enum bb_return_values { Unsat = 0, Sat = 1, Timeout = 2, Failure = 3, Simplified = 4 };
extern char *bb_return_val_names[5];

int bb_satsolve_satz( int numvar, int numclause, int * wff, 
			int * soln, int maxtime, int argc, char * argv[] );
int bb_satsolve_relsat( int numvar, int numclause, int * wff, 
			int * soln, int maxtime, int argc, char * argv[] );
int bb_satsolve_walksat( int numvar, int numclause, int * wff, 
			int * soln, int maxtime, int argc, char * argv[] );
int bb_satsolve_chaff( int numvar, int numclause, int * wff, 
			int * soln, int maxtime, int argc, char * argv[] );

int bb_simplifier_compact(int numvararg, int numclausearg, int * wff,
			  int * newnumclause, int maxtime,
			  int argc, char * argv[]);

/* Approximate rates: how many iterations to check the clock */
#define Graphplan_Rate  100
#define Satz_Rate  20
#define Walksat_Rate  500
#define Relsat_Rate  100

/*******************************************************************************/
/*       Default solver arguments                                              */
/*******************************************************************************/
/*
#define BB_DEFAULT_ARGS \
    "-solver", "-maxsec", "30", "graphplan", "-then", \
    "-maxsec", "0", "compact", "-l", "-then", \
    "satz", "-cutoff", "20", "-restart", "10", "-then", \
    "satz", "-cutoff", "40", "-restart", "5", "-then", \
    "satz", "-cutoff", "80", "-restart", "5", "-then", \
    "satz", "-cutoff", "200"
    */
#define BB_DEFAULT_ARGS \
    "-solver", "-maxsec", "0", "chaff"


/*******************************************************************************/
/*       Following are used to connect graphplan/planner/graph2ff              */
/*******************************************************************************/

extern int bb_axioms;

extern int bb_maxsec;
extern int bb_maxit;
extern long bb_current_it;

extern int bb_numvar;
extern int bb_numclause;

extern int * bb_wff;
extern int bb_wff_len;
extern int bb_wff_buflen;

extern int * bb_soln;
extern int bb_soln_len;
extern int bb_soln_buflen;

void bb_init_limitp(int maxsec, int maxit);
void bb_graph2wff(int maxtime, int num_goals);
void bb_soln2graph(void);

extern int bb_prettyflag;

extern int bb_printflag;
enum bb_printmasks { PrintLit = 1, PrintCNF = 2, PrintExit = 4, PrintMap = 8, PrintModel = 16};


void bb_parse_solver_args(int i, int argc, char * argv[]);
void bb_default_solver_args(int helpmode);
void bb_reparse_graphplan_options(int argc, char * argv[]);

enum bb_solver_types { Anysat, Graphplan, Compact };


typedef struct bb_solver_spec_struct
{
    int maxit;
    int maxsec;
    int solver;
    int argc;
    char ** argv;
    int (*proc)(int, int, int *, int *, int, int, char * [] );
} bb_solver_spec;

extern int bb_spec_len;
extern bb_solver_spec bb_spec[20];

double elapsed_seconds(void);

enum BB_OutputValues { 
    BB_OutputOpMutex = 1,	/* should always be 1 */
    BB_OutputOpPre = 2,		/* should always be 1 */
    BB_OutputFactFrame = 4,	/* should always be 1 */
    BB_OutputFactMutex = 8,	/* may be 0 or 1 */
    BB_OutputOpEffect = 16,	/* may be 0 or 1 */
    BB_OutputRedundant = 32,	/* may be 0 or 1 -- only has effect if FactMutex and OpEffect also 1 */
    BB_OutputSymmetric = 64,    /* should be 0, unless you want to duplicate original wffs */
    BB_OutputOpPreOp = 128,     /* may be 0 or 1 */
    BB_OutputActDefs = 256      /* may be 0 or 1 */
};  /* Good values: 
       1+2+4 = 7 = most simple translation (default);
       1+2+4+8 = 15 = includes all mutexes;
       1+2+4+8+16 = 31 = most compact translation; 
       1+2+4+8+16+32 = 63 = most informative translation;
       1+128 = 129 = action only translation;
       1+2+4+8+16+32+256 = 319 = defined actions (dagsat);
    */
