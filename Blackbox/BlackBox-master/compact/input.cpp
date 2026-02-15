#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>

#include "tab.h"
#include "stack.h"

#include "../interface.h"
#include "compact.h"

extern int mvar;
extern struct stack *all_clauses;
extern struct stack *clean_clauses;
extern struct stack *input_lits;
extern int max_var;
extern struct var *var_array;
extern signed char *val;
#ifdef BINARY_COUNT
extern signed char *pbin, *nbin;
#endif

/*
struct stack *clause_get();
int cleanup_clause();
struct stack *copy_stack(); */

int * global_wff;
int global_unread_clauses;

int input_wff(int numvararg, int numclausearg, int * wff)
{
  struct stack *text;

  global_wff = wff;
  global_unread_clauses = numclausearg;

  while(1) {
    if (clause_get(&text) == NULL) break; /* end of input */
    if (! empty_stack(text)) {
	if (assert_clause(text)== Unsat) return Unsat;
    }
  }

#ifdef DEBUG
  printf("Input literals: ");
  print_stack(input_lits);
  printf("\n");
  printf("Input clauses: ");
  map_stack(all_clauses,print_stack(*ptr));
  printf("\n");
#endif
  return Simplified;
}

/* Returns -1 if contradiction */
int assert_clause(struct stack *text)
{
  struct clause *clause;
  int len;
  int i;
  int answ;

  spush(copy_stack(text),all_clauses);

  if ((answ=cleanup_clause(text)) == Sat) return(Simplified); /* Clause cleaned up into tautology */
  if (answ == Unsat) return(Unsat);

  spush(copy_stack(text),clean_clauses);
  len=stack_length(text);
    
  if (len==1) {
    if (!try_assign(ftop(text))) {
      printf("Contradiction after unit resolution.\n");
      return(Unsat);
    }
    return(Simplified);
  }

  if (len==2) {
    int first = ftop(text), second = fsecond(text);
    struct var *fs=&var_array[abs(first)], *ss=&var_array[abs(second)];

    if (first>0) {spush(second,fs->neg_hits);}
    else spush(second,fs->pos_hits);

    if (second>0) {spush(first,ss->neg_hits);}
    else spush(first,ss->pos_hits);

#ifdef BINARY_COUNT
    incf_bin(first); incf_bin(second);
#endif
  }
  /* Don't need clause struct for binary clauses: */
  if (len==2) return(Simplified);

  clause = ((struct clause *) malloc(sizeof(struct clause)));
  clause->text = text;
  clause->terms = len;
  clause->deleted=0;

#ifdef DEBUG
  print_clause(clause);
#endif

  /* index clauses of length 3 or more */
  if(len==2) return(Simplified);
  map_stack(text,
	    {if (*ptr > 0) {spush(clause,var_array[abs(*ptr)].pos_clauses);}
	    else {spush(clause,var_array[abs(*ptr)].neg_clauses);}});
  return Simplified; /* Missing return in original code? - H.Kautz */
}

/* Try_Assign is like value, but no unit resolution is done --
instead x is pushed onto a stack to be unit resolved latter.
*/
int
try_assign(int x)
{
#ifdef DEBUG
  printf("Setting %d.\n",x);
#endif
  if (val[abs(x)]==0) {
    val[abs(x)]=sign(x);
    spush(x,input_lits);
  }
  else return(val[abs(x)]==sign(x));
}


int cleanup_clause(struct stack *text)
{
  /* int opposite_val(); */

  /* Delete the clause if it is subsumed by a literal or if it contains x and -x */
  map_stack(text,
	    {if (val[abs(*ptr)] == sign(*ptr)) return(Sat);
	     if (stack_find(text,-(*ptr))) return(Sat);});

  stack_delete_if(text,opposite_val);

  if (empty_stack(text)) {
      printf("Contradiction after unit resolution.\n");
      return(Unsat);
  }

  stack_remove_duplicates(text);
  return(Simplified);
}

int
opposite_val(int x)
{
  return(val[abs(x)] == -sign(x));
}


/* Reads a single line of input as a stack.
   Returns NULL on EOF or %. */
struct stack *clause_get(struct stack **s)
{
  int x,r;

  *s = new_stack(3);
  while((r = read_int(&x)) != EOF) {
    if (x == 0) break;
    if (abs(x)>=mvar) {
      fprintf(STDMSG,"Variable %d exceeds maximum %d.\n",x,mvar);
      exit(1);
      /* not reachable! */
    }
    if (abs(x)>max_var) max_var=abs(x);
    spush(x,*s);
  }
  return((r == EOF && (empty_stack(*s))) ? NULL : *s);
}


/* Returns EOF on % or EOF.  Else sets x to zero on end of line, or to next integer */
/*
read_int(iop,x)
register FILE *iop;
int *x;
{
  register int c;

  while (! numberp(c = getc(iop))) {
    if (c == '%') return(EOF);
    if (c == EOF) return(EOF);
    if (c == '\n') {*x=0; return(0);}
  }
  ungetc(c,iop);
  fscanf(iop,"%d",x);
  return(0);
}
*/


int
read_int(int *x)
{
    if (global_unread_clauses <= 0) return EOF;
    *x = *(global_wff++);
    if ((*x)==0) global_unread_clauses--;
    return 0;
}

int
numberp(int x)
{
  return(isdigit(x) || (x == '-'));
}

void
print_clause(struct clause *c)
{
  print_stack(c->text);
  printf(" terms: %d:\n",c->terms);
}

void
print_var(int var, struct var *st)
{
  printf("\n\n%d pos_hits: ",var);
  print_stack(st->pos_hits);
  printf("\n  neg_hits: ");
  print_stack(st->neg_hits);
  printf("\n  pos_clauses:\n");
  map_stack(st->pos_clauses,print_clause((struct clause *)*ptr));
  printf("\n  neg_clauses:\n");
  map_stack(st->neg_clauses,print_clause((struct clause *)*ptr));
  printf("\n");
}


