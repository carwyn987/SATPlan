#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <math.h>
#ifndef WIN32
#include <sys/time.h>
#endif


#include "../interface.h"
#include "tab.h"
#include "stack.h"
#include "compact.h"

/* This program uses the data structures and unit propagator from tableau.
 * but its purpose is to do a series of polynomial time simplifications.
 * To use this program undefine BINARY_COUNT so that ur will not expect it.
*/


int dump_flag;

int max_var;          /* largest var seen in theory */
int vars_valued;

struct stack *all_clauses=NULL; /* text of all clauses */
struct stack *clean_clauses=NULL; /* text of all clauses (after call to cleanup) */
struct stack *ur_stack=NULL;    /* literals to be unit propagated */
struct stack *input_lits=NULL;  /* literals in input */
struct stack *scratch;          /* Scratch space used internally by check_singletons */

struct var *var_array;          /* array of information about vars */

int level;
struct stack *undo_stack[MAX_LEVEL]; /* array of pointers to stacks of pointers to counters
					decremented in current level */
struct stack *undo;                  /* Always points to current undo stack */
signed char *val_stack[MAX_LEVEL];          /* stack storing old variable values for
					backtracking */
signed char *val;                           /* current variable values */

struct stack *to_branch;
signed char to_branch_flag;

/*
struct stack *new_stack();
struct stack *append();
struct stack *copy_stack(); */

int mvar=VARS;
FILE *table_file=NULL;

int lambda_x;                   /* you don't want to know */

/* external functions */
int input_wff(int numvararg, int numclausearg, int * wff);

int bb_simplifier_compact(int numvararg, int numclausearg, int * wff,
		      int * newnumclause, int maxtime, int argc, char * argv[])
{
  int i;
  char filename[100];
  int itlimit;


  int pure_lit_flag=0, singleton_flag=0, resolve_flag=0;
  int unary_failed_lit_flag=0, binary_failed_lit_flag=0;

  fprintf(STDMSG, "Invoking simplifier compact\n");

  dump_flag = 0;
  itlimit = 2;

  /* Parse command line arguments */
  while ((--argc > 0) && (*++argv)[0] == '-')
    switch ((*argv)[1]) {
    case 'h':
	printf("Use: compact -l (unary) -b (binary) -s (singleton) -p (pure) -d (dump) -i N (binary iteration limit, default 2)\n");
	return Failure;
	break;
    case 'i':
	argv++; argc--;
	if (sscanf(*argv, "%d", &itlimit)!=1) {
	    printf("compact: bad argument\n");
	    exit(1);
	}
	break;
    case 'b':
      binary_failed_lit_flag=1;
      if (argc > 1 && argv[1][0] != '-'){
	  argv++; argc--;
	  if (sscanf(*argv, "%d", &itlimit)!=1) {
	      printf("compact: bad argument\n");
	      exit(1);
	  }
      }
      break;
    case 'p':
      pure_lit_flag=1;
      break;
    case 'd':
      dump_flag=1;
      break;
    case 's':
      singleton_flag=1;
      break;
    case 'l':
      unary_failed_lit_flag=1;
      break;
    /*case 'r':
      resolve_flag=1;
      break;*/
    case 'v':
      sscanf(*argv,"-v%d",&mvar);
      break;
    case 'f':
      if (sscanf(*argv,"-f%s",filename)>0) {
	if ((table_file=fopen(filename,"w"))==NULL) {
	  fprintf(STDMSG,
		  "WARNING: Attempt to open translation table file %d failed.\n",filename);
	}
      }
      else 
	fprintf(STDMSG,
		"WARNING: no name given for translation table.  Use 'compact -f<filename>'.\n");
      break;
    default:
      printf("compact: illegal option\n");
      exit(1);
    }

  init_tab(numvararg);

  if (numvararg>VARS){
      fprintf(STDMSG, "ERROR: too many variables\n");
      return Failure;
  }

  if (input_wff(numvararg, numclausearg, wff)==Unsat) return Unsat;   /* This inputs the theory and sets max_var to largest var in theory */
  ur_stack = new_stack(max_var);
  while(! empty_stack(input_lits)) /* Unit prop input literals */
    if (!(ur(fpop(input_lits)))) {
	fprintf(STDMSG,"Contradiction after unit resolution.\n");
	return Unsat;
    }

#ifndef SILENT
  fprintf(STDMSG,"Loaded.  Max var: %d.\n",max_var);
#endif
#ifdef TRACE
  fprintf(STDMSG,"Initial variable values:[");
  for(i=0;i<max_var;i++)
    if (val[i]>0) {fprintf(STDMSG," %d",i);} else if (val[i]<0) fprintf(STDMSG," %d",-i);
  fprintf(STDMSG,"]\n");
  dump_theory();
#endif

  /*printf("\nINITIAL THEORY");
  for(i=1;i<=max_var;i++) print_var(i,&var_array[i]);*/

  /*show_stats();*/

  if (unary_failed_lit_flag && binary_failed_lit_flag) {
    fprintf(STDMSG,"Warning: Binary failed lit option overrides unary failed lit option\n");
    unary_failed_lit_flag=0;
  }
  if (unary_failed_lit_flag || binary_failed_lit_flag) {
      if (unary_failed_lit()==Unsat) return Unsat;}
  if (binary_failed_lit_flag) {
      if (binary_failed_lit(itlimit)==Unsat) return Unsat;}

  if (singleton_flag) {
      if (resolve_singletons()==Unsat) return Unsat;}
  /*if (resolve_flag) obvious_resolutions();*/
  if (pure_lit_flag) pure_literal_rule();

  /*printf("\nFINAL THEORY");
  for(i=1;i<=max_var;i++) print_var(i,&var_array[i]);*/


  /* dump_theory(); */

  dump_no_renum(wff, newnumclause);
  return Simplified;
}


int resolve_singletons()
{
  int i;
  int answ;

  for(i=1;i<=max_var;i++)
    if (val[i]==0) {
	if ((answ = check_singleton(i))== -1) return Unsat;
	if (! answ) answ = check_singleton(-i);
	if (answ == -1) return Unsat;
    }

  unlink_deleted_clauses();
  return Simplified;
}

int clause_deleted(int x)
{
  return ((struct clause *) x)->deleted;
}

void
unlink_deleted_clauses()
{
  int i;
  /* int clause_deleted(); */

  for(i=1;i<=max_var;i++) {
    stack_delete_if( var_array[i].neg_clauses, clause_deleted);
    stack_delete_if( var_array[i].pos_clauses, clause_deleted);
  }
}

/* In unsat case, returns -1 not Unsat */
int check_singleton(int x)
{
  struct stack *clauses = ((x<0) ? var_array[-x].neg_clauses : var_array[x].pos_clauses);
  struct stack *hits = ((x<0) ? var_array[-x].pos_hits : var_array[x].neg_hits);
  int occurs=0;

  /* First count the occurances of x */
  map_stack(clauses,
	    if (((struct clause *) *ptr)->deleted) continue;
	    if (!COM_redundant(((struct clause *) *ptr)->text)) if (++occurs==2) return(0););
  map_stack(hits,
	    if (val[abs(*ptr)]==0) if (++occurs==2) return(0););

  if (occurs==0) {
    /*printf("%d does not occur.  Valueing %d.\n",x,-x);*/
    value(-x); return(1);}  /* Degenerate case */

  /*printf("Resolving out the singleton %d.\n",x);*/
  /* Map over all clauses containing x */
  map_stack(clauses,
	    struct stack *text = ((struct clause *) *ptr)->text;
	    if (((struct clause *) *ptr)->deleted) continue;
	    if (!COM_redundant(text)) {
	      make_empty(scratch);
	      copy_stack_data(scratch,text);
	      stack_delete(scratch,x);
	      if (resolve_against(scratch,x)==Unsat) return -1;});
  map_stack(hits,
	    make_empty(scratch);
	    spush(*ptr,scratch);
	    if (resolve_against(scratch,x)==Unsat) return -1;);
  
  /* Finally we completely remove x and -x (and all clauses mentioning them) */
  blast_var(abs(x));
  return(1);
}


int resolve_against(struct stack *text, int x)
{
  struct stack *r;

  stack_delete(text,x);

  /* We resolve against the occurances of -x */
  map_stack(((-x<0) ? var_array[x].neg_clauses : var_array[-x].pos_clauses),
	    if (((struct clause *) *ptr)->deleted) continue;
	    r = append(((struct clause *) *ptr)->text,text);
	    stack_delete(r,-x);
	    /*printf("Resolvant: ");
	    map_stack(r,printf(" %d",*ptr););
	    printf("\n");*/
	    if (assert_clause(r)==Unsat)return Unsat;);
  map_stack(((-x<0) ? var_array[x].pos_hits : var_array[-x].neg_hits),
	    r = copy_stack(text);
	    spush(*ptr,r);
	    /*printf("Resolvant: ");
	    map_stack(r,printf(" %d",*ptr););
	    printf("\n");*/
	    if (assert_clause(r)==Unsat)return Unsat;);
  return Simplified;
}


/* and if you think this will work... */
void
blast_var(int x)
{
  /* int contains_var_x(); */
  struct var *xs = &var_array[x];

  map_stack(xs->pos_hits,if (*ptr>0) {stack_delete(var_array[*ptr].neg_hits,-x);}
	                else stack_delete(var_array[-*ptr].pos_hits,-x));
  map_stack(xs->neg_hits,if (*ptr>0) {stack_delete(var_array[*ptr].neg_hits,x);}
	                else stack_delete(var_array[-*ptr].pos_hits,x));

  map_stack(xs->pos_clauses,delete_clause(((struct clause *) *ptr)));
  map_stack(xs->neg_clauses,delete_clause(((struct clause *) *ptr)));

  make_empty(xs->pos_hits);
  make_empty(xs->neg_hits);
  make_empty(xs->pos_clauses);
  make_empty(xs->neg_clauses);

  lambda_x = x;
  stack_delete_if(clean_clauses,contains_var_x);
}

int
contains_var_x(struct stack *s)
{
  return(stack_find(s,lambda_x) || stack_find(s,-lambda_x));
}

void
delete_clause(struct clause *c)
{
  c->deleted=1;
}


void
pure_literal_rule()
{
  int i;

  for(i=1;i<=max_var;i++) {
    if (val[i]==0) 
      if (!check_lit(i))
	check_lit(-i);
  }
}

int
check_lit(int x)
{
  struct stack *clauses = ((x<0) ? var_array[-x].neg_clauses : var_array[x].pos_clauses);
  struct stack *hits = ((x<0) ? var_array[-x].pos_hits : var_array[x].neg_hits);

  map_stack(clauses,if (!COM_redundant(((struct clause *) *ptr)->text)) return(0));
  map_stack(hits,if (val[abs(*ptr)]==0) return(0));
  /*printf("Setting %d by pure literal rule\n",-x);*/
  value(-x);
  return(1);
}

int unary_failed_lit()
{
  int i,change;
  int iteration=1;

  while (1) {
    int unew=0;
    change=0;
    fprintf(STDMSG,"Iteration %d: ",iteration++);

    for(i=1;i<=max_var;i++) {
      int v;
      if (val[i]!=0) continue;
      new_level();
      v = value(i);
      end_level();
      if (!v) {
	if (!value(-i)) {
	    fprintf(STDMSG,"Contradiction after failed lit test.\n"); 
	    return Unsat;
	}
	change=1; unew++;
      }
      new_level();
      v = value(-i);
      end_level();
      if (!v) {
	value(i);
	change=1; unew++;
      }
    }
    fprintf(STDMSG,"unary implicates %d\n", unew);
    if (!change) break;
  }
  return Simplified;
}


int binary_failed_lit(int itlimit)
{
  int i,j,change=0;
  struct stack *s;
  int iteration=1;

#ifdef TRACE
  printf("Starting binary_failed_lit\n");
#endif
  int k;

  k=0;
  while (++k <= itlimit) {
    int new_unary=0, new_binary=0;
    change=0;
    fprintf(STDMSG,"Iteration %d: ",iteration++);

    for(i=1;i<=max_var;i++) {
      int v;
      if (val[i]!=0) continue;

      /* Unary implcates */
      new_level(); v = value(i); end_level();
      if (!v) {
	change=1; new_unary++;
	if (!value(-i)) {
	    fprintf(STDMSG,"Contradiction after failed lit test.\n"); 
	    return Unsat;
	}
	continue;
      }
      new_level(); v = value(-i); end_level();
      if (!v) {
	change=1; new_unary++;
	value(i);
	continue;
      }

      /* Binary implicates */
      make_empty(to_branch); to_branch_flag=1;
      new_level(); value(i);
      to_branch_flag=0;
      map_stack(to_branch,
		int j = -(*ptr);

	  if (val[abs(j)]!=0) continue;
	  /* continue if j<i ?? */

	  new_level(); v = value(j); end_level();
	  if (!v) {
	    change=1; new_binary++;
	    if (!value(-j)) {	/* j and -j both give contradiction.  -i is implicate. */
	      new_binary--; new_unary++;
	      end_level();
	      if (!value(-i))
		{fprintf(STDMSG,"Contradiction after failed lit test.\n"); 
		return Unsat;}
	      goto next_i;
	    }
	    end_level();		/* Have to add the new clause at the base level */
	    s = new_stack(3);
	    fpush(-i,s); fpush(-j,s);  
	    if (assert_clause(s)==Unsat) return Unsat;
	    new_level(); value(i);
	  }
	      );
      end_level();

      make_empty(to_branch); to_branch_flag=1;
      new_level(); value(-i);
      to_branch_flag=0;
      map_stack(to_branch,
		int j = -*ptr;
	  if (val[abs(j)]!=0) continue;
	
	  new_level(); v = value(j); end_level();
	  if (!v) {
	    change=1; new_binary++;
	    if (!value(-j)) {	/* j and -j both give contradiction.  i is implicate. */
	      new_binary--; new_unary++;
	      end_level();
	      if (!value(i))
		{fprintf(STDMSG,"Contradiction after failed lit test.\n"); 
		return Unsat;}
	      goto next_i;
	    }
	    end_level();		/* Have to add the new clause at the base level */
	    s = new_stack(3);
	    fpush(i,s); fpush(-j,s); 
	    if (assert_clause(s)==Unsat)return Unsat;
	    new_level(); value(-i);
	  }
		);
      end_level();
    next_i:;
    }
    fprintf(STDMSG,"unary implicates %d  binary implicates %d\n",new_unary,new_binary);
    if (!change) return Simplified;
  }
  return Simplified;
}

void
new_level()
{
#ifdef TRACE
  printf(" n");
#endif
  level++;
  memcpy(val_stack[level],val,(1+max_var)*sizeof(signed char));   val = val_stack[level];
  make_empty(undo_stack[level]);
  undo = undo_stack[level];
}

void
end_level()
{
  register int *ptr;
  int *top = undo->fill_ptr;

#ifdef TRACE
  printf(" e");
#endif
  for(ptr=undo->bottom; ptr < top; ptr++) (* ((int *) *ptr))++;
  level--;
  undo = undo_stack[level];
  val = val_stack[level];
}

void
show_stats()
{
  int i;

  printf("%15s %15s %15s","Var","Pos occurs","Neg occurs\n");
  for(i=1;i<=max_var;i++)
    printf("%15d %15d %15d\n",
	   i, 
	   stack_length(var_array[i].pos_clauses) + stack_length(var_array[i].neg_hits),
	   stack_length(var_array[i].neg_clauses) + stack_length(var_array[i].pos_hits));
}
    
void
dump_theory()
{
    int *top = clean_clauses->fill_ptr;
    register int *ptr = clean_clauses->bottom;
    struct stack *text;

    int *map;
    int i;

    printf("Dumping theory (%d clauses)\n",stack_length(clean_clauses));

    /* map = ((int *) malloc(mvar * sizeof(int))); */
    map = ((int *) malloc((max_var+10) * sizeof(int)));


    for(i=0;i<=max_var;i++) map[i]=0;
    i=1;

    for(;ptr<top;ptr++) {              /* for each clause */
	text = ((struct stack *) *ptr);
	if (! COM_redundant(text)) {
	    register int *ptr2 = text->bottom;
	    int *top2 = text->fill_ptr;
	    printf("(");
	    for(;ptr2<top2;ptr2++)   /* for each literal in the clause */
		if (val[abs(*ptr2)] == 0) {
		    if (map[abs(*ptr2)] == 0) /* if this var has not been seen before */
			map[abs(*ptr2)] = i++;
		    printf("%d ",sign(*ptr2) * map[abs(*ptr2)]);
		    /*printf("%d ",*ptr2);*/
		}
	    printf(")\n");
	}
    }
    printf("%%\n0\n");
    /*fprintf(STDMSG,"New max literal: %d.\n",i-1);*/
    if (table_file!=NULL) {
	for(i=1;i<=max_var;i++) {
	    if (map[i]==0) {/* This old variable does map to anything in new theory */
		if (val[i]==0) {
		    /* Variable can be assigned either value.  Just set to F*/
		    fprintf(table_file,"%d -2\n",i);
		}
		else {
		    fprintf(table_file,"%d %d\n",i,(val[i]==1 ? -1 : -2));
		}
	    }
	    else {
		fprintf(table_file,"%d %d\n",i,map[i]);
	    }
	}
    }
}




void
dump_no_renum(int * wff, int * newnumclause)
{
    int *top = clean_clauses->fill_ptr;
    register int *ptr = clean_clauses->bottom;
    struct stack *text;

    int *map;
    int i;
    int clauses_output;
    int forced_true, forced_false;

    forced_true = 0;
    forced_false = 0;

    if (dump_flag) printf("Dumping simplified theory (%d clauses)\n"
			  "begin simplified-cnf\n",
			  stack_length(clean_clauses));

    /* map = ((int *) malloc(mvar * sizeof(int))); */
    map = ((int *) malloc((max_var+10) * sizeof(int)));
    for(i=0;i<=max_var;i++) map[i]=0;
    i=1;
    clauses_output = 0;

    for(;ptr<top;ptr++) {              /* for each clause */
	text = ((struct stack *) *ptr);
	if (! COM_redundant(text)) {
	    register int *ptr2 = text->bottom;
	    int *top2 = text->fill_ptr;
	    /* printf("("); */
	    for(;ptr2<top2;ptr2++)   /* for each literal in the clause */
		if (val[abs(*ptr2)] == 0) {
		    if (map[abs(*ptr2)] == 0) /* if this var has not been seen before */
			map[abs(*ptr2)] = i++;
		    /* printf("%d ",sign(*ptr2) * map[abs(*ptr2)]); */
		    *(wff++) = *ptr2;
		    if (dump_flag) printf("%d ",*ptr2);
		}
	    /* printf(")\n"); */
	    *(wff++) = 0;
	    if (dump_flag) printf("0\n");
	    clauses_output++;
	}
    }

    for(i=1;i<=max_var;i++) {
	if (map[i]==0) {/* This old variable does map to anything in new theory */
	    if (val[i]==0 || val[i]==-1){
		/* Variable can be assigned either value.  Just set to F*/
		/* fprintf(table_file,"%d -2\n",i); */
		*(wff++) = -i;
		*(wff++) = 0;
		if (dump_flag) printf("%d 0\n", -i);
		clauses_output++;
		forced_false++;
	    }
	    else {
		*(wff++) = i;
		*(wff++) = 0;
		if (dump_flag) printf("%d 0\n", i);
		clauses_output++;
		forced_true++;
	    }
	}
    }
    if (dump_flag) printf("end simplified-wff\n");

    * newnumclause = clauses_output;

    printf("Variables forced true: %d\n", forced_true);
    printf("Variables forced false: %d\n", forced_false);
    printf("Clauses output: %d\n", clauses_output);
    printf("Variables undetermined: %d\n", max_var - forced_true - forced_false);
    printf("Non-unary clauses output: %d\n", clauses_output - forced_true - forced_false);
}


void
init_tab(int numvararg)
{
  int i;

  max_var = 0;
  vars_valued = 0;

  /* Alloc space for variable size arrays */
  /*
  var_array = ((struct var *) malloc(mvar * sizeof(struct var)));
  for(i=0;i<MAX_LEVEL;i++) val_stack[i] = ((signed char *) malloc(mvar * sizeof(signed char)));
  */
  var_array = ((struct var *) malloc((numvararg+10) * sizeof(struct var)));
  for(i=0;i<MAX_LEVEL;i++) val_stack[i] = ((signed char *) malloc((numvararg+10) * sizeof(signed char)));

  val = val_stack[0];

  /* If we run multiple times we really should recollect this storage */
  all_clauses = new_stack(100);
  clean_clauses = new_stack(100);
  /* ur_stack initialized in main routine */
  input_lits = new_stack(10);

  for(i=1;i<=numvararg;i++) {
    var_array[i].pos_hits = new_stack(10);
    var_array[i].neg_hits = new_stack(10);
    var_array[i].pos_clauses = new_stack(10);
    var_array[i].neg_clauses = new_stack(10);
    val[i] = 0;
  }
  for(i=0;i<MAX_LEVEL;i++) {
    undo_stack[i] = new_stack(10);
  }
  undo = undo_stack[0];

  level=0;

  scratch = new_stack(10);
  to_branch = new_stack(100);
}

void
obvious_resolutions()
{
  int i;

  for(i=1;i<=max_var;i++) if (val[i]==0) 
    map_stack(var_array[i].pos_clauses,
	      if (maybe_resolve(((struct clause *) *ptr)->text,i)) {
	        blast_clause(((struct clause *) *ptr));
	      });
}

/* This is not currently used (and may or may not work) */
int
maybe_resolve(struct stack *text, int x)
{
  int l1,l2,l3;

  /* for now only handle the length 3 case */
  if (stack_length(text) != 3) return(0);
  l1 = ftop(text);
  l2 = fsecond(text);
  l3 = fthird(text);
  if (l1 == x) l1 = l3;
  if (l2 == x) l2 = l3;
  /* Now we know that l1 and l2 are the two elements of text != x. */

  map_stack(var_array[x].neg_clauses,
	    if (stack_find(((struct clause *) *ptr)->text,l1) &&
		stack_find(((struct clause *) *ptr)->text,l2)) {
	      struct stack *nc=copy_stack(((struct clause *) *ptr)->text);
	      stack_delete(nc,-x);
	      fprintf(STDMSG,"FOUND RESOLUTION\n");
	      assert_clause(nc);
	      blast_clause(((struct clause *) *ptr));
	      return(1);
	    });
  return(0);
}

void
blast_clause(struct clause* c)
{
  map_stack(c->text,
	    if (*ptr>0) {
	      stack_delete(var_array[*ptr].pos_clauses, (int)c); }
	    else 
	      stack_delete(var_array[-*ptr].neg_clauses,(int)c));
}
