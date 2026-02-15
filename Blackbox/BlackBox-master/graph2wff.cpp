//#ifndef WIN32
//#include <sys/time.h>
//#include <sys/times.h>
//#include <unistd.h>
//#else
//#include "win32/adns/adns.h"
//#include <time.h>
//#endif

// Commented out the adns stuff - HAK
#include <sys/time.h>
#include <sys/times.h>
#include <unistd.h>
#include <time.h>

// Why on earth did CLK_TCK disappear from time.h with g++ version 4.0?
#ifndef CLK_TCK
#ifdef CLOCKS_PER_SEC
#define CLK_TCK CLOCKS_PER_SEC
#else
#define CLK_TCK 60
#endif
#endif

#include <stdlib.h>
#include <sys/types.h>
#include <limits.h>
#include "interface.h"
#include "graphplan.h"
#include "control.h"
#include "utilities.h"

#ifdef BBCTRL
void bb_generate_wffctrl (int);
void eval_generate_wffctrl(wffctrl_list ctrl, fact_list scope, 
			   instantiation_list insts, int len);
void generate_wffctrl(wffctrl_list ctrl, instantiation_list insts, int len);

extern int control_mode;
extern wffctrl_list wffctrls;
extern char *bbun_str; 
#endif
extern struct timeval start, end;
extern int max_global_sec;
extern int bb_stop;

char *bb_return_val_names[5] = { "Unsat", "Sat", "Timeout", "Failure", "Simplified" };

int bb_number_action_vars;
int bb_number_fluent_vars;

int bb_printflag;
int bb_prettyflag;

int bb_maxsec;
int bb_maxit;

#ifndef WIN32
struct tms bb_buffer;
#endif

long bb_starttick;
long bb_maxticks;
clock_t bb_currenttick;
long bb_current_it;
int bb_muststop;
int bb_firstk;

void bb_init_limitp(int maxsec, int maxit)
{
    bb_maxit = maxit;
    bb_current_it = 0;

    bb_maxticks = (long)(CLK_TCK * maxsec);
#ifndef WIN32
    times(&bb_buffer);
    bb_starttick = bb_buffer.tms_utime + bb_buffer.tms_stime;
#else
    bb_starttick = (long)clock();
#endif

    bb_muststop = FALSE;
}

int bb_limitp(int rate)
{


    if (bb_muststop) return TRUE;
    bb_current_it++;
    if (bb_maxit && (bb_current_it >= bb_maxit)) {
	bb_muststop = TRUE;
	return TRUE;
    }
    if (bb_maxticks && bb_current_it % rate == 0){

      /* No good reason for the following, and it makes cygwin dump core mysteriously...*/
      /* gettimeofday(&end,0); */

#ifndef WIN32
	times(&bb_buffer);
        bb_currenttick = bb_buffer.tms_utime + bb_buffer.tms_stime;
#else
        bb_currenttick = clock();
#endif
	if ((bb_currenttick - bb_starttick) >= bb_maxticks){
	    bb_muststop = TRUE;
	    return TRUE;
	}
    }
    return FALSE;
}

/************************************************/
/*  lists                                       */
/************************************************/

#define Appendi(list, i) {\
    if (list ## _len >= list ## _buflen) Stretchi(&list, &list ## _buflen);\
    list[ list ## _len ++ ] = i; }

#define Appendp(list, p) {\
    if (list ## _len >= list ## _buflen) Stretchp(&list, &list ## _buflen);\
    list[ list ## _len ++ ] = p; }

void Stretchi(int ** list, int * buflen)
{
    if ((*buflen)<=0){
	*list = (int *) malloc((size_t)(sizeof(int)*1024));
	*buflen = 1024;
    }
    else {
	*list = (int *) realloc(*list, (size_t)(sizeof(int)*(*buflen)*2));
	*buflen *= 2;
    }
}

void Stretchp(vertex_t ** list, int * buflen)
{
    if ((*buflen)<=0){
	*list = (vertex_t *) malloc((size_t)(sizeof(void *)*1024));
	*buflen = 1024;
    }
    else {
	*list = (vertex_t *) realloc(*list, (size_t)(sizeof(void *)*(*buflen)*2));
	*buflen *= 2;
    }
}

/************************************************/
/*  converting graph to wff                     */
/************************************************/

int bb_numvar;
int bb_numclause;

int * bb_wff;
int bb_wff_len;
int bb_wff_buflen = 0;

int * bb_soln;
int bb_soln_len;
int bb_soln_buflen = 0;

vertex_t * bb_prop2vertex;
int bb_prop2vertex_len;
int bb_prop2vertex_buflen = 0;


void bb_generate_fact_mutex(hashtable_t t, int stamp)
{
  vertex_t vert;
  edgelist_t edge;

  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0) continue;
    if ((edge = vert->exclusive) != NULL) {
	for(; edge; edge = edge->next){
	    if (edge->endpt->needed == 0) continue;
	    if (!(bb_axioms & BB_OutputSymmetric) && (vert->prop > edge->endpt->prop)) continue;
	    bb_numclause++;
	    if (bb_printflag & PrintLit) fprintf(STDDATA, "( NOT %s-%d    NOT %s-%d )\n", vert->name, stamp, edge->endpt->name, stamp); 
	    Appendi(bb_wff, -(vert->prop));
	    Appendi(bb_wff, -(edge->endpt->prop));
	    Appendi(bb_wff, 0);
	}
    }
  }
}


int redundant_by_effect(vertex_t opa, vertex_t opb)
{
    vertex_t facta, factb;
    edgelist_t edgea, edgeb;

    if (!(bb_axioms & BB_OutputOpEffect)) return 0;

    for (edgea = opa->out_edges; edgea; edgea = edgea->next){
	facta = edgea->endpt;
	if (facta->needed == 0) continue;
	for (edgeb = opb->del_edges; edgeb; edgeb = edgeb->next){
	    factb = edgeb->endpt;
	    if (facta == factb) return 1;
	}
	if (bb_axioms & BB_OutputFactMutex){
	    for (edgeb = opb->out_edges; edgeb; edgeb = edgeb->next){
		factb = edgeb->endpt;
		if (are_mutex(facta, factb)) return 1;
	    }
	}
    }
    for (edgea = opa->del_edges; edgea; edgea = edgea->next){
	facta = edgea->endpt;
	if (facta->needed == 0) continue;
	for (edgeb = opb->out_edges; edgeb; edgeb = edgeb->next){
	    factb = edgeb->endpt;
	    if (facta == factb) return 1;
	}
    }
    return 0;
}


int redundant_by_precondition(vertex_t opa, vertex_t opb)
{
    vertex_t facta, factb;
    edgelist_t edgea, edgeb;

    if (!(bb_axioms & BB_OutputFactMutex)) return 0;
    if (!(bb_axioms & BB_OutputOpPre)) return 0;

    for (edgea = opa->in_edges; edgea; edgea = edgea->next){
	facta = edgea->endpt;
	if (facta->needed == 0) continue;
	for (edgeb = opb->in_edges; edgeb; edgeb = edgeb->next){
	    factb = edgeb->endpt;
	    if (are_mutex(facta, factb)) return 1;
	}
    }
    return 0;
}


int redundant_op_mutex(vertex_t opa, vertex_t opb)
{
    if (!(bb_axioms & BB_OutputSymmetric) && (opa->prop > opb->prop)) return 1;
    if (bb_axioms & BB_OutputRedundant) return 0;
    if (redundant_by_effect(opa, opb) || 
	redundant_by_precondition(opa, opb)) return 1;
    return 0;
}

void bb_generate_op_mutex(hashtable_t t, int stamp)
{
  vertex_t vert;
  edgelist_t edge;

  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0) continue;
    if ((edge = vert->exclusive) != NULL) {
	for(; edge; edge = edge->next){
	    if (edge->endpt->needed == 0) continue;
	    if (redundant_op_mutex(vert, edge->endpt)) continue;
	    bb_numclause++;
	    if (bb_printflag & PrintLit) fprintf(STDDATA, "( NOT %s-%d    NOT %s-%d )\n", vert->name, stamp, edge->endpt->name, stamp); 
	    Appendi(bb_wff, -(vert->prop));
	    Appendi(bb_wff, -(edge->endpt->prop));
	    Appendi(bb_wff, 0);
	}
    }
  }
}

void bb_generate_frame(hashtable_t t, int stamp, int simplified)
{
  vertex_t vert;
  vertex_t op;
  edgelist_t edge;

  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0) continue;

    /* note that at maxtime you know for sure the precondition
       of axiom holds, so you can eliminate it */

    if (simplified){
	if (bb_printflag & PrintLit) fprintf(STDDATA, "( ");
    }
    else {
	if (bb_printflag & PrintLit) fprintf(STDDATA, "( NOT %s-%d    ", vert->name, stamp);
    }

    if (! simplified) Appendi(bb_wff, -(vert->prop));

    for (edge = vert->in_edges; edge; edge = edge->next){
	op = edge->endpt;
	if (op->needed == 0) continue;
	if (bb_printflag & PrintLit) fprintf(STDDATA, " %s-%d ", op->name, stamp);
	Appendi(bb_wff, op->prop);
    }
    bb_numclause++;
    if (bb_printflag & PrintLit) fprintf(STDDATA, " )\n");
    Appendi(bb_wff, 0);
  }
}

void bb_generate_op_pre_op(hashtable_t t, int stamp, int highest)
{
    /* For each action in the list, and then for each precondition of the action,
       add the axiom that the action implies the disjunction of adders of the
       precondition.
       This condition replaces both OpPre and FactFrame. */
  vertex_t vert;
  vertex_t fact;
  edgelist_t edge;
  edgelist_t predge;
  vertex_t act;

  /* Nothing to do if we are at the earliest action layer */
  if (stamp <= 1) return;

  /* At the last action layer, may need to generate top-level disjunctive actions */
  if ((stamp == highest) && !(bb_axioms & BB_OutputFactFrame)){
      bb_generate_frame(fact_table[highest], highest, TRUE);
  }

  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0) continue;
    for (edge = vert->in_edges; edge; edge = edge->next){
	fact = edge->endpt;
	if (fact->needed == 0) continue;

	bb_numclause++;
	if (bb_printflag & PrintLit) fprintf(STDDATA, "( NOT %s-%d ", vert->name, stamp);
	Appendi(bb_wff, - (vert->prop));

	for (predge = fact->in_edges; predge; predge = predge->next){
	    act = predge->endpt;
	    if (act->needed == 0) continue;
	    if (bb_printflag & PrintLit) fprintf(STDDATA, " %s-%d ", act->name, stamp-1);
	    Appendi(bb_wff, act->prop);
	}
	Appendi(bb_wff, 0);
	if (bb_printflag & PrintLit) fprintf(STDDATA, " )\n");
    }
  }
}

void bb_generate_actdefs(hashtable_t t, int stamp)
{
    /* Generate definitions for the actions that could be recognized by dagsat.
       This procedure generates the head clauses:
       action <- (precondition & effects)
       The contrapositive 
       action -> preconditions
       action -> effects
       is generated by bb_generate_precond and bb_generate_effect.
       Note that for dagsat to recognize the definition, the head clauses
       must appear first in the wff, and the action must be the first
       literal in each clause.
    */

  vertex_t vert;
  vertex_t fact;
  edgelist_t edge;

  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0) continue;

    bb_numclause++;
    if (bb_printflag & PrintLit) { 

	fprintf(STDDATA, "C DEFINITION\n");

	fprintf(STDDATA, "( %s-%d ", vert->name, stamp);
    }
    Appendi(bb_wff, (vert->prop));

    for (edge = vert->in_edges; edge; edge = edge->next){
	fact = edge->endpt;
	if (fact->needed == 0) continue;

	if (bb_printflag & PrintLit) fprintf(STDDATA, " NOT %s-%d ", fact->name, stamp-1);
	Appendi(bb_wff, - (fact->prop));
    }
    for (edge = vert->out_edges; edge; edge = edge->next){
	fact = edge->endpt;
	if (fact->needed == 0) continue;
	if (bb_printflag & PrintLit) fprintf(STDDATA, " NOT %s-%d ", fact->name, stamp);
	Appendi(bb_wff, - (fact->prop));
    }
    for (edge = vert->del_edges; edge; edge = edge->next){
	fact = edge->endpt;
	if (fact->needed == 0) continue;
	if (bb_printflag & PrintLit) fprintf(STDDATA, " %s-%d ", fact->name, stamp);
	Appendi(bb_wff, (fact->prop));
    }

    if (bb_printflag & PrintLit) fprintf(STDDATA, " )\n");
    Appendi(bb_wff, 0);
  }
}
  
void bb_generate_precond(hashtable_t t, int stamp)
{
  vertex_t vert;
  vertex_t fact;
  edgelist_t edge;

  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0) continue;
    for (edge = vert->in_edges; edge; edge = edge->next){
	fact = edge->endpt;
	if (fact->needed == 0) {
	    fprintf(STDMSG,"***ERROR**** unneeded precondition for %s-%d\n", vert->name, stamp);
	}
	bb_numclause++;
	if (bb_printflag & PrintLit) fprintf(STDDATA, "( NOT %s-%d    %s-%d )\n", vert->name, stamp, fact->name, stamp-1);
	Appendi(bb_wff, - (vert->prop));
	Appendi(bb_wff, fact->prop);
	Appendi(bb_wff, 0);
    }
  }
}


void bb_generate_effect(hashtable_t t, int stamp)
{
  vertex_t vert;
  vertex_t fact;
  edgelist_t edge;

  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0) continue;
    for (edge = vert->out_edges; edge; edge = edge->next){
	fact = edge->endpt;
	if (fact->needed != 0) {
	    bb_numclause++;
	    if (bb_printflag & PrintLit) fprintf(STDDATA, "( NOT %s-%d    %s-%d )\n", vert->name, stamp, fact->name, stamp);
	    Appendi(bb_wff, - (vert->prop));
	    Appendi(bb_wff, fact->prop);
	    Appendi(bb_wff, 0);
	}
    }
    for (edge = vert->del_edges; edge; edge = edge->next){
	fact = edge->endpt;
	if (fact->needed != 0) {
	    bb_numclause++;
	    if (bb_printflag & PrintLit) fprintf(STDDATA, "( NOT %s-%d    NOT %s-%d )\n", vert->name, stamp, fact->name, stamp);
	    Appendi(bb_wff, - (vert->prop));
	    Appendi(bb_wff, - (fact->prop));
	    Appendi(bb_wff, 0);
	}
    }
  }
}

void bb_assign_prop_table(hashtable_t t, int stamp)
{
    vertex_t vert;

    get_next(t, 0); /* get ready */
    while((vert = get_next(t, 1)) != NULL) {
	if (vert->needed == 0) continue;
	vert->prop = ++ bb_numvar;
	if (bb_printflag & PrintMap)
	    fprintf(STDDATA, "a %d %s-%d\n", vert->prop, vert->name, stamp);
	Appendp(bb_prop2vertex, vert);
    }
}

void bb_assign_prop(int len, int num_goals, int acts_only)
{
    int i;

    bb_numvar = 0;
    bb_prop2vertex_len = 0;
    Appendp(bb_prop2vertex, NULL);

    for (i = 0; i < len; i++)
      bb_assign_prop_table(op_table[i], i+1);

    bb_number_action_vars = bb_numvar;

    /* for branching only on operators */
    bb_firstk = bb_numvar;

    if (!acts_only){
	for(i=0; i <= len; ++i) {
	    bb_assign_prop_table(fact_table[i], i);
	}
    }
    bb_number_fluent_vars = bb_numvar - bb_number_action_vars;
    bb_soln_len = 0;
    Appendi(bb_soln, 0);
    for (i=1; i<=bb_numvar; i++)
	Appendi(bb_soln, 0);

    fprintf(STDMSG, "number of action variables = %d\n", 
	    bb_number_action_vars);
    fprintf(STDMSG, "number of fluent variables = %d\n", 
	    bb_number_fluent_vars);
    /* fprintf(STDMSG, "bb_soln array length %d out of %d\n", bb_soln_len, bb_soln_buflen); */
}


void bb_generate_wff(int len, int num_goals)
{
  int i;
  vertex_t v;
  int acts_only;

  acts_only = !(bb_axioms & (BB_OutputOpPre | BB_OutputFactFrame | 
			     BB_OutputFactMutex | BB_OutputOpEffect ));

  remove_unneeded_vertices(len);
  bb_assign_prop(len, num_goals, acts_only);
  fprintf(STDMSG, "total number variables = %d\n", bb_numvar);
  bb_numclause = 0;
  bb_wff_len = 0;

  if (bb_printflag & PrintLit) fprintf(STDMSG, "Begin literal wff\n");

  /* print mutex and backward chaining */
  for(i=0; i < len; ++i) {
      if (bb_axioms & BB_OutputActDefs) bb_generate_actdefs(op_table[i], i+1);
      if (bb_axioms & BB_OutputOpPre) bb_generate_precond(op_table[i], i+1);
      if (bb_axioms & BB_OutputOpEffect) bb_generate_effect(op_table[i], i+1);
  }
  for(i=0; i < len; ++i) {
      if (bb_axioms & BB_OutputFactFrame) bb_generate_frame(fact_table[i+1], i+1, (i+1)==len);
      if (bb_axioms & BB_OutputOpMutex) bb_generate_op_mutex(op_table[i], i+1);
      if (bb_axioms & BB_OutputFactMutex) bb_generate_fact_mutex(fact_table[i+1], i+1);
      if (bb_axioms & BB_OutputOpPreOp) bb_generate_op_pre_op(op_table[i], i+1, len);
  }

  /* print initial facts */
  /* probably not necessary, but cannot hurt and useful for debugging */
  if (bb_axioms & BB_OutputOpPre){
      get_next(fact_table[0],0);
      while((v = get_next(fact_table[0],1)) != NULL) {
	  if (v->needed == 0) continue;
	  if (v->is_true == 1){ /* should always hold, because of setup() */
	      bb_numclause++;
	      if (bb_printflag & PrintLit) fprintf(STDDATA, "( %s-%d )\n", v->name, 0);
	      Appendi(bb_wff, v->prop); 
	      Appendi(bb_wff, 0);
	  }
      }
  }

  /* print goals */
  /* also probably not necessary, due to special handling of frame axioms */
  if (bb_axioms & BB_OutputFactFrame){
      for(i=0; i < num_goals; ++i) {
	  bb_numclause++;
	  if (goals_at[len][i]->needed == 0) continue;
	  if (bb_printflag & PrintLit) fprintf(STDDATA, "( %s-%d )\n",goals_at[len][i]->name, len);
	  Appendi(bb_wff, goals_at[len][i]->prop);
	  Appendi(bb_wff, 0);
      }
  }

  if (bb_printflag & PrintLit) fprintf(STDMSG, "End literal wff\n");
  fprintf(STDMSG, "number clauses = %d\n", bb_numclause);

#ifdef BBCTRL
  if (control_mode)
    bb_generate_wffctrl(len);
#endif
}

void bb_print_cnf(void)
{
    int i,j;

    fprintf(STDMSG, "Begin cnf wff\n");
    fprintf(STDDATA, "p cnf %d %d\n", bb_numvar, bb_numclause);
    i=0; j = -1;
    while (i<bb_numclause){
	do {
	    fprintf(STDDATA, " %d", bb_wff[++j]);
	} while (bb_wff[j] != 0);
	fprintf(STDDATA, "\n");
	i++;
    }
    fprintf(STDMSG, "End cnf wff\n");
}

/************************************************/
/*  main routine                                */
/************************************************/

void bb_graph2wff(int maxtime, int num_goals)
{
    fprintf(STDMSG,"Converting graph to wff\n");
    bb_generate_wff(maxtime, num_goals);
    if (bb_printflag & PrintCNF) bb_print_cnf();
    if (bb_printflag & PrintExit) exit(0);
}

/************************************************/
/* removing redundant actions 			*/
/************************************************/
/*
void bb_rmredundant_action(int maxtime, int num_goals)
{
  int i, t, num_goals_at, new_num_goals;
  // vertex_t v;
  edgelist_t e, e2;

  num_goals_at = num_goals;
  for (t = maxtime; t > 0; t--) {
    new_num_goals = 0;
    for (i = 0; i < num_goals_at; i++) {
      for (e = goals_at[t][i]->in_edges; e; e = e->next) {
	if (e->endpt->used == 2) {
	  e->endpt->used = 1;
	  // printf("%s\n", e->endpt->name);
	  for (e2 = e->endpt->in_edges; e2; e2 = e2->next) {
	    goals_at[t-1][new_num_goals++] = e2->endpt; 
	  }
	}
      }
    }
    num_goals_at = new_num_goals;
  }

  for (i = 1; i < bb_firstk; i++) {
    if (bb_prop2vertex[i]->used == 2)
      printf("%s\n", bb_prop2vertex[i]->name);
  } 
} */

/***********************************************/
/*  convert solution back to graph             */
/***********************************************/

void bb_soln2graph(void)
{
    int i;

    if (bb_printflag & PrintModel) fprintf(STDDATA, "Begin model\n");
    for (i=1; i<=bb_numvar; i++){
	//bb_prop2vertex[i]->is_true = bb_soln[i];
	bb_prop2vertex[i]->used = bb_soln[i];
	if (bb_printflag & PrintModel){
	    fprintf(STDDATA, " %d", bb_soln[i] ? i : -i);
	    if (i % 10 == 0) fprintf(STDDATA, "\n");
	}
    }
    if (bb_printflag & PrintModel) fprintf(STDDATA, "\nEnd model\n");
}

/************************************************/
/*  solver specificiations                      */
/************************************************/

int bb_spec_len = 0;
bb_solver_spec bb_spec[20];

void bb_parse_solver_args(int i, int argc, char * argv[])
{
    int k, a;
    int (*p)(int, int, int *, int *, int, int, char * [] );

    p = NULL;
    k = 0;
    bb_spec_len = 0;
    i++;
    while (i < argc){
	if (strcmp(argv[i], "-maxsec")==0){
	    if (++i >= argc) do_error("command line args not in proper format");
	    sscanf(argv[i], "%d", &bb_maxsec);
	}
	else if (strcmp(argv[i], "-maxit")==0){
	    if (++i >= argc) do_error("command line args not in proper format");
	    sscanf(argv[i], "%d", &bb_maxit);
	}
	else {

	    k = bb_spec_len++;

	    bb_spec[k].solver = Anysat;
	    if (strcmp(argv[i], "graphplan")==0){
		p = NULL;
		bb_spec[k].solver = Graphplan;
	    }
	    else if (strcmp(argv[i], "compact")==0){
		bb_spec[k].solver = Compact;
		p = & bb_simplifier_compact;
	    }
	    else if (strcmp(argv[i], "satz")==0)
		p = & bb_satsolve_satz;
	    else if (strcmp(argv[i], "walksat")==0)
		p = & bb_satsolve_walksat;
	    else if (strcmp(argv[i], "chaff")==0)
		p = & bb_satsolve_chaff;
	    else do_error("command line args not in proper format");
	    
	    bb_spec[k].maxsec = bb_maxsec;
	    bb_spec[k].maxit = bb_maxit;
	    bb_spec[k].argv = &argv[i];
	    bb_spec[k].proc = p;

	    a = 1;
	    while ( ++i < argc && strcmp(argv[i], "-then")!=0 ) a++;
	    bb_spec[k].argc = a;
	}
	i++;
    }
}


void bb_print_solver_spec(void)
{
    int i,j;

    fprintf(STDMSG, "Begin solver specification\n");
    for (i=0; i<bb_spec_len; i++){
	fprintf(STDMSG,"    -maxint %8d   -maxsec %8f ", bb_spec[i].maxit, (double)bb_spec[i].maxsec);
	for (j=0; j<bb_spec[i].argc; j++){
	    fprintf(STDMSG, " %s", bb_spec[i].argv[j]);
	}
	fprintf(STDMSG, "\n");
    }
    fprintf(STDMSG, "End solver specification\n");
}



void bb_reparse_graphplan_options(int argc, char * argv[])
{
    int i,j;
    char * option;

    for(j = 1; j < argc; ++j) {
	if (strcmp(argv[j], "-O")==0 && j+1 < argc){
	    option = argv[++j];

	    do_subsets = 0;
	    do_irrel = 0;
	    do_buildup = 0;
	    do_greedy = 0;
	    do_lower = 0;
	    do_noexcl = 0;
	    for(i=0; option[i] != '\0'; ++i) {
		if (option[i] == 'S') {
		    do_subsets = 1; 
		    fprintf(STDMSG, "Graphplan option: S == subsets\n");
		    do_completeness = 0;}
		if (option[i] == 'I') {
		    fprintf(STDMSG, "Graphplan option: I == irrelevent\n");
		    do_irrel = 1; }
		if (option[i] == 'B') {
		    fprintf(STDMSG, "Graphplan option: B == buildup\n");
		    do_buildup = 1; }
		if (option[i] == 'G') {
		    fprintf(STDMSG, "Graphplan option: G == greedy\n");
		    do_greedy = 1; }
		if (option[i] == 'L') { 
		    fprintf(STDMSG, "Graphplan option: L == lower bound\n");
		    do_lower = 1; do_completeness = 0;  }
		if (option[i] == 'E') {
		    fprintf(STDMSG, "Graphplan option: E == no exclusiveness\n");
		    do_noexcl = 1; }
	    }
	}
	else {
	    fprintf(STDMSG, "Bad argument to graphplan\n");
	    exit(1);
	}
    }
}

void bb_graphplan_help(void)
{
    fprintf(STDMSG, "Options for graphplan solver are:\n"
    "\t-O <option list> where\n"
    "\tI = look for irrelevants\n"
    "\tL = Lower bound time needed by counting steps\n"
    "\tB = Build up to goals\n"
    "\tE = Don't do mutual exclusions (for testing)\n"
    "\tS = examine subsets\n");
}

char * bb_default_argstring[] = { BB_DEFAULT_ARGS };
char * bb_satz_argstring[] = { "-solver", "satz" };
char * bb_help_argv[] = { "dummy", "-help" };


void bb_default_solver_args(int helpmode)
{
    int i;

    if (helpmode){
	for (i=0; i<bb_spec_len; i++){
	    if (bb_spec[i].solver == Graphplan)
		bb_graphplan_help();
	    else
		(void)(* (bb_spec[i].proc))(0, 0, NULL, NULL, 0, 
                                            2, bb_help_argv);
	}
	exit(1);
    }

    if (bb_spec_len == 0){

	if (bb_printflag){
	    bb_parse_solver_args(0, 2, bb_satz_argstring);
	    return;
	}

	bb_parse_solver_args(0, sizeof bb_default_argstring / sizeof bb_default_argstring[0], 
			     bb_default_argstring);
    }
    bb_print_solver_spec();
}


/*
 * Adding control to wff
 */

#ifdef BBCTRL
void bb_generate_wffctrl (int len)
{
  wffctrl_list ctrl;

  fprintf(STDMSG, "Generating control wff\n");
  for (ctrl = wffctrls; ctrl; ctrl = ctrl->next) {
    eval_generate_wffctrl(ctrl, ctrl->scope, NULL, len);
  }
  fprintf(STDMSG, "%d clauses\n", bb_numclause);
}

void eval_generate_wffctrl(wffctrl_list ctrl, fact_list scope, 
			   instantiation_list insts, int len)
{
  int tval = 0;
  char *fname = scope->item->item;
  // char str[100];
  fact_list fact;
  token_list var;
  instantiation_list inst_var;

  if (strcmp(fname, "forall") == 0) {
    fact = scope->next;
    var = make_generator(fact->item, scope->item->next, insts, len);
//    print_token_list(STDMSG, var);
    inst_var = (instantiation_list)malloc(sizeof(instantiation_s));
    inst_var->var_part = fact->item->item;
    inst_var->next = insts;
    for (; var && tval == 0 ; var = var->next) {
      inst_var->const_part = var->item;
      eval_generate_wffctrl(ctrl, scope->body, inst_var, len);
    }
    free_token_list(var); 
    inst_var->next = NULL;
    free_instantiation(inst_var); 
  }
  else {	/* evaluate */
//    printf("%s\n", fname);
//    print_instantiation(insts);
    if (eval(scope, insts, len)) {
      generate_wffctrl(ctrl, insts, len);
    }
  }
}

int generate_control_literal (token_list token, instantiation_list insts,
			      int sign, int time, int len, int not_flag,
			      int *type_flag)
{
  token_list tmp;
  char str[100];
  vertex_t vert;
  int value;

  if (strcmp(token->item, DELETE) == 0) {
    return generate_control_literal (token->next, insts, -sign, time, len, 1, 
				     type_flag);
  }
  if (strcmp(token->item, "next") == 0) {
    return generate_control_literal(token->next, insts, sign, time + 1, len, 0,
				    type_flag);
  }
  tmp = NULL;
  if (not_flag) {
    if (lookup_negation_predicate (token->item)) {
      sprintf(str, bbun_str, token->item);
      tmp = strdup2token(str);
      token = tmp;
      sign = sign * -1;
    }
  }
  value = 0;
  instantiate_into_string(token, insts, str, 0);
  if ((time < len) && (vert = lookup_from_table(fact_table[time], str))) {
    value = (sign * vert->prop);
  }
  *type_flag = (not_flag) ? 1 : 0;
  
  if (tmp)
    free_token_list (tmp);
  return value;
}

void generate_wffctrl(wffctrl_list ctrl, instantiation_list insts, int len)
{
  int ok;
  int clause_len;
  int clause[50];
  int type_flag, nprev;
//  char str1[50];
//  char str[5][50];
  fact_list fact;

  for (int i = 0; i < len; i++) {
    clause_len = 0;
    ok = 1;
    for (fact = ctrl->preconds; fact; fact = fact->next) {
      clause[clause_len] = generate_control_literal (fact->item, insts, -1, 
						     i, len, 0, &type_flag);
      if (clause[clause_len] == 0) {
	if (ctrl->condflag == WFF_FORCE_MODE) {
	  continue;
	}
        ok = 0;
	continue;
      }
//      instantiate_into_string(fact->item, insts, str1, 0);
//      strcpy(&(str[clause_len][0]), str1);
      clause_len++;
    }
    nprev = clause_len;
    if (nprev == 0 && ctrl->condflag == WFF_FORCE_MODE) ok = 1;
    if (ok) {
      for (fact = ctrl->effects; fact; fact = fact->next) {
	clause[clause_len] = generate_control_literal (fact->item, insts, 1, 
						       i, len, 0, &type_flag);
	if (clause[clause_len] == 0) {
	    ok = 0;
	    break;
	}
	if (nprev == 0 && type_flag == 0) {
	  ok = 0;
	  break;
	}
//	instantiate_into_string(fact->item, insts, str1, 0);
//	strcpy(&(str[clause_len][0]), str1);
	clause_len++;
      }
      if (ok) {
//        printf("%d %s %s %s\n", i, str[0], str[1], str[2]);
//        printf("%d %d %d %d\n", i, clause[0], clause[1], clause[2]);
	bb_numclause++;
	for (int j = 0; j < clause_len; j++) 
	  Appendi(bb_wff, clause[j]);
	Appendi(bb_wff, 0);  
      }
    }
  }
}

#endif
