#define VARS 100000
#define MAX_LEVEL 10
#define MAXTERMS 5
#define LEVEL_CUTOFF 100000000 /* 100 million */

/* This value is returned by cbl if it detects a contradiction */
#define CONTRADICTION -1


struct clause {
  int terms;
  int pos_terms;
  int deleted;       /* set to 1 when clause deleted by singleton resolution */
  struct stack *text;
};

struct var {
  struct stack *pos_hits;
  struct stack *neg_hits;
  struct stack *pos_clauses;
  struct stack *neg_clauses;
};


#define	abs(x) ((x) < 0 ? -(x) : (x))
#define min(x,y) ((x<y) ? x : y)
#define max(x,y) ((x<y) ? y : x)
#define	sign(x) ((x) < 0 ? -1 : 1)

/* #define DEBUG 1 */
/* #define MEM_DEBUG 1 */
/*#define ARI_COMPILER 1*/
/*#define TRACE 1*/
#define SILENT 1

#ifdef BINARY_COUNT

#define incf_bin(x) ((x) < 0 ? nbin[-(x)]++ : pbin[(x)]++)
#define decf_bin(x) ((x) < 0 ? nbin[-(x)]-- : pbin[(x)]--)
#define get_bin(x) ((x) < 0 ? nbin[-(x)] : pbin[(x)])

#endif
