/****************************************************************/
/* learn.c							*/
/* revised: Aug., 2000						*/
/* written by: Yi-Cheng Huang 1999				*/
/****************************************************************/

#include <math.h>
//#include <values.h>
#include "interface.h"
#include "utilities.h"
#include "control.h"
#include "tim.h"
#include "learn.h"
#include "verify.h"
#include "bbio.h"

double elapsed_seconds(void);	/* function in satz-rand */

#ifdef BBLEARN

//#define BBDEBUG

extern op_list ops;
extern fact_list the_goals;
extern int global_maxtime;
extern propspace_ptr propspaces;
extern fact_list predicates, constants;
extern token_list negation_predicates, objects;
extern hashtable_t *fact_table, *op_table, goal_table; 
extern defpred_list dps;
extern control_list controls;
extern wffctrl_list wffctrls;
extern FILE *learnfp;

int num_action_precond;
int num_ex, orig_num_ex;
int num_attr, orig_num_attr, new_num_attr;
vertex_t ex_node[MAX_NUM_TABLE_EXAMPLE];
char *ex_table[MAX_NUM_TABLE_EXAMPLE][MAX_NUM_ATTRIBUTE];
int ex_id[MAX_NUM_TABLE_EXAMPLE];
int ex_time[MAX_NUM_TABLE_EXAMPLE];
int ex_type[MAX_NUM_TABLE_EXAMPLE], ex_type_backup[MAX_NUM_TABLE_EXAMPLE]; 
/* attribute types. note: start from [1]. [0] is the composite type */
int attr_type[MAX_NUM_ATTRIBUTE];
literal_elt ex_literals[MAX_NUM_ATTRIBUTE];

literal_elt rule_literals[MAX_NUM_ATTRIBUTE+MAX_NUM_RULE_BODY_LITERAL];
literal_elt rule_body[MAX_NUM_RULE_BODY_LITERAL];
	
int num_rule_lit;
int num_rule_body_lit;
int rule_obj_type
    [MAX_NUM_ATTRIBUTE+MAX_NUM_RULE_BODY_LITERAL][MAX_NUM_PRED_VAR + 1];
double rule_body_gain[MAX_NUM_ATTRIBUTE+MAX_NUM_RULE_BODY_LITERAL];
int rule_lit_seqno[MAX_NUM_ATTRIBUTE+MAX_NUM_RULE_BODY_LITERAL];
int cur_seqno, bt_seqno;
char* attr_type_name[MAX_NUM_ATTRIBUTE];

int num_pos_ex, num_neg_ex;	/* number of postive and negative examples */
int phase;
op_ptr cur_op;
literal_ptr action_precond_literals, action_effect_literals;
literal_elt best_lit;
int best_obj_type[MAX_NUM_PRED_VAR + 1];
int gain_heuristics = 1;
int ex_heuristics = 1;
int learn_bt_flag = 1;
double best_gain, ex_table_info_bits;

/* use this for unknown attributes */
char none_str[] = "(none)";

learned_rule_ptr learned_rules;
int K;

#ifdef BBDEBUG

/********************************************************
 * routines for debugging				*
 ********************************************************/
void
print_ex_table (void)
{
  int i, j, zz;
  zz = num_attr;
  printf("+++++++++++++++++++++++++++\n");
  printf("%s\n", cur_op->name);
  for (i = 0; i < zz; i++)
    printf ("%d ", attr_type[i]);
  printf ("\n");
  for (i = 0; i < zz; i++) {
    if (ex_literals[i].lit_type >= PRED_LIT) {
      if (ex_literals[i].bk_type == GOAL)
	printf ("GOAL:");
      else
	if (ex_literals[i].bk_type == STATIC)
	  printf ("STATIC:");
      printf ("%s", ex_literals[i].lit_name);
      for (j = 1; j <= get_predicate_variable_number(ex_literals[i].lit_name);
	   j++)
	printf ("[%d](%d)", ex_literals[i].binding[j], ex_literals[i].bind_type[j]);
      printf (" ");
    }
    else
      printf ("(none) ");
  }
  printf ("\n");
  for (i = 0; i < num_ex; i++) {
    printf ("%2d %d %2d", ex_id[i], ex_time[i] + 1, ex_type[i]);
    for (j = 0; j < num_attr; j++)
      printf (" %s", ex_table[i][j]);
    printf ("\n");
  }
  printf("+++++++++++++++++++++++++++\n");
}

void 
print_literal (literal_ptr lit)
{
  if (lit->lit_type == EQUAL_LIT)
    printf ("=");
  else if (lit->lit_type == UNEQUAL_LIT)
    printf ("!=");
  else if (lit->lit_type == PRED_LIT)
    printf("%s", lit->lit_name);
  else if (lit->lit_type == NOT_PRED_LIT)
    printf("!%s", lit->lit_name);
    
  for (int i = 1; i <= lit->num_var; i++)
    printf("[%d]", lit->binding[i]);
  printf ("  ");
  if (lit->bk_type == GOAL)
    printf("GOAL");
  else if (lit->bk_type == STATIC)
    printf("STATIC");
  else printf ("DYNAMIC");
  printf ("\n");
}

void
print_backup_rule ()
{
  int i;
  for (i = 0; i < num_rule_lit; i++)
    print_literal (&(rule_literals[i]));
  printf("----------\n");
  for (i = 0; i < num_rule_body_lit; i++)
    print_literal (&(rule_body[i]));
}


void
print_rule (void)
{
  int i;
  printf ("%s Find a rule ==> \n", cur_op->name);
  for (i = 0; i < num_rule_body_lit; i++)
    print_literal(&(rule_body[i]));
  printf("=======================================\n");
}



void 
print_action_literals (void)
{
  literal_ptr lit;
  
  for (lit = action_precond_literals; lit; lit = lit->next) {
    print_literal(lit);
    printf("changed = %d\n", lit->changed);
  }
  printf("------------------\n");
  for (lit = action_effect_literals; lit; lit = lit->next) 
    print_literal(lit);
}

#endif


/************************************************************************
 * routines for learning control rules					*
 ************************************************************************/

double
info_bits (int pos, int neg)
{
  int total = pos + neg;
  if (total == 0 || pos == 0)
    return NO_GAIN;
  switch (gain_heuristics) {
  case 1:
    if (neg == 0)
      return (double)1.0;
    return (double)(pos + 1) / (double)(pos + neg + 2);
  case 2:
  case 3:
    return (log((double)pos / (double)total) / log(2.0));
  }
  return NO_GAIN;
}

/* calculate the information gain 				        */
/* k is the number of positive examples included by adding the literal  */
/* see Quinlan 1996 for details						*/
double
info_gain (int pos, int neg, int k)
{ 
  if (gain_heuristics == 3)
    return (double)k * (ex_table_info_bits - info_bits(pos, neg));
  return info_bits(pos, neg);
}

void
calculate_ex_table_info_bits (void)
{
  int i, type;
  for (i = num_pos_ex = num_neg_ex = 0; i < num_ex; i++) {
    type = ex_type[i];
    if (type == POS_EX) 
      num_pos_ex++;
    else
      if (type == NEG_EX)
	num_neg_ex++;
  }
  ex_table_info_bits = info_bits(num_pos_ex, num_neg_ex);
  // printf ("pos = %d, neg = %d, info = %f\n", pos, neg, ex_table_info_bits);
}


void 
literal_copy (literal_ptr lit_s, literal_ptr lit_d)
{
  int i, num_var, *binding_d, *binding_s;
  lit_d->lit_name = lit_s->lit_name;
  lit_d->lit_type = lit_s->lit_type;
  lit_d->bk_type = lit_s->bk_type;
  lit_d->num_var = num_var = lit_s->num_var;
  lit_d->rule_lit_type = lit_s->rule_lit_type;
  binding_d = lit_d->binding;
  binding_s = lit_s->binding;
  for (i = 1; i <= num_var; i++)
    binding_d[i] = binding_s[i];
}

void
obj_type_copy (int *src, int *dest)
{
  for (int i = 1; i < MAX_NUM_PRED_VAR + 1; i++) {
    dest[i] = src[i];
  }
}

/* free action literals */
void
free_literals (literal_ptr literals)
{
  literal_ptr lit;
  while (literals != 0) {		
    lit = literals;
    literals = literals->next;
    free(lit);
  }
}

void 
free_action_literals (void)
{
  int i;
  free_literals(action_precond_literals);
  free_literals(action_effect_literals);
  for (i = 0; i < MAX_NUM_ATTRIBUTE; i++) {
    attr_type[i] = 0; 
  } 
}

/* seperate a string by CONNECTOR 		*/
/* return the last location in the string 	*/
char *
seperate_string (char *src, char *dest)
{
  for(; (*src != '\0') && (*src != CONNECTOR); *dest++ = *src++);
  *dest = '\0';
  return (*src == '\0') ? 0 : ++src;
}

/* count the number of parameters for an action */
int
action_parameter_count (op_ptr op)
{
  int i = 0;
  fact_list p;
  for (p = op->params; p; p = p->next, i++);
  return i;
}


/* initialize the examples table */
void 
init_ex_table (void)
{
  num_ex = num_attr = 0;
//  for (i = 0; i < MAX_NUM_ATTRIBUTE; i++) {
//    num_attr_type[i] = 0;
//    attr_type[i] = 0; 
//    literals[i].lit_type = NO_LIT;
//  } 
}

/* find the parameter location in the action */
int 
find_param_location (char *pname)
{
  int i = 0;
  fact_list param;
  for (param = cur_op->params; param; param = param->next, i++) {
    if (strcmp(param->item->item, pname) == 0)
      return i;
  }
  return -1;
}

void
build_action_literals (literal_ptr *action_literals, fact_list fact, int flag)
{
  int i, j, not_flag;
  int binding[MAX_NUM_PRED_VAR + 1];
  int num_var;
  char *name;
  token_list token;
  fact_list p;
  literal_ptr lit, ex_lit;
  propspace_ptr ps;
  
  if (flag)
    num_action_precond = 0;
  for (p = fact; p; p = p->next) {
    if (flag)
      num_action_precond++;
    if (strcmp(p->item->item, DELETE) == 0) {
      token = p->item->next;
      not_flag = 1;
    }
    else {
      token = p->item;
      not_flag = 0;
    }
    name = token->item;
    num_var = get_predicate_variable_number(name);
    for (i = 1, token = token->next; i <= num_var; i++, token = token->next) {
      binding[i] = find_param_location(token->item);
    }
    ex_lit = 0;
    if (flag && num_var == 1 && find_predicate_type(name) == STATIC) {
      ps = find_property_space(name, 1);
      ps = ps->root;
      if (ps->type == ATTRIBUTE) {
	j = binding[1];
	attr_type_name[j] = name;
	ex_lit = &ex_literals[j];
	for (i = 1; i <= ps->num_obj_types; i++) {
	  attr_type[j] |= ps->obj_types[i - 1];
//	  printf ("attribute: %d\n", j);
	}
      }
    }
    lit = (literal_ptr)calloc(1, sizeof (literal_elt));   
    lit->lit_name = name;
    lit->lit_type = (not_flag) ? NOT_PRED_LIT : PRED_LIT;
    lit->num_var = num_var;
    lit->bk_type = find_predicate_type(name);
    lit->next = 0;
    for (i = 1; i <= num_var; i++)
      lit->binding[i] = binding[i];
    if (ex_lit)
      literal_copy(lit, ex_lit);
    if (*action_literals) {
      lit->next = *action_literals;
    }
    *action_literals = lit;
  }
}

/*
void
mark_changed_literals (void)
{
  int i;
  literal_ptr plit, elit;

  for (plit = action_precond_literals; plit; plit = plit->next) {
    if (find_predicate_type(plit->lit_name) == DYNAMIC)
      plit->changed = 1;
    else {
      for (elit = action_effect_literals; elit; elit = elit->next) {
	if ((strcmp(plit->lit_name, elit->lit_name) == 0) &&
	    (plit->lit_type != elit->lit_type)) {
	  for (i = 1; i <= plit->num_var; i++) {
	    if (plit->binding[i] != elit->binding[i]) {
	      break;
	    }
	  }
	  if (i <= elit->num_var)
	    continue;
	  else
	    break;
	}
      }
      plit->changed = (elit) ? 1 : 0;
    }
  }
}
*/

/* initialize the examples literals and action precondition literal 	*/
/* return the number of preconditions of the action			*/
void
init_action_ex_literals (void)
{
  action_precond_literals = action_effect_literals = 0;  
  build_action_literals(&action_precond_literals, cur_op->preconds, 1);
  build_action_literals(&action_effect_literals, cur_op->effects, 0);
}

/* check out whether the action is doable in the DYNAMIC plan or not */
int
action_doable (char *action_name, vertex_t action, int num_precond,
	       int rule_type)
{
  int i, flag;
  edgelist_t e;
  char str[100];
  vertex_t v;

  if (action->used)
    return 1;
  if (action->is_true == NODE_COVERED)
    return 0;
  for (i = 0, e = action->in_edges; e; e = e->next, i++) {
    if (e->endpt->is_true == 0)
      return 0;
  }
  if (i < num_precond)
    return 0;


  if (phase == STATIC)
    return 1;
  flag = 0;
  for (e = action->exclusive; e; e = e->next) {
    v = e->endpt;
    seperate_string(v->name, str);
    if ((ex_heuristics == 1) && (strcmp(str, action_name) == 0) && v->used) 
      return 0;
    if (v->used && !IS_NOOP(v))
      flag = 1;
  }
  return flag;
}

/* collect positive and negative examples from the plan */
void 
collect_examples (int rule_type)
{
  int i, j, type;
  char str[100], *s;
  vertex_t v;

  num_attr = action_parameter_count(cur_op);
  for (i = 0; i < global_maxtime; i++) {
    get_next(op_table[i],0);
    while((v = get_next(op_table[i], 1)) != NULL) {
      if (!IS_NOOP(v)) {
	s = seperate_string(v->name, str);
	if ((strcmp(str, cur_op->name) == 0) && 
	    action_doable(str, v, num_action_precond, rule_type)) {
	  ex_id[num_ex] = num_ex;
	  ex_time[num_ex] = i;
	  ex_node[num_ex] = v;
	  for (j = 0; j < num_attr; j++) {
	    s = seperate_string(s, str);
	    ex_table[num_ex][j] = find_object_type(str, &type);
	  }
	  // printf("%d %2d %s\n", i + 1, ex_type[num_ex], v->name);
	  num_ex++;
	}
      }
    }
  }
  orig_num_ex = num_ex;
  orig_num_attr = num_attr;
}

/* compare a literal with the fields.		*/
/* return 1: if unequal 0: equal		*/
int 
literal_comp (literal_ptr lit, char *lit_name, int binding[], int obj_type[],
	      int num_var, int num_newvar, int bk_type)
{
  int j, bind, lit_bind, matched_num_newvar = 0, same_index, ot, flag;


  if (lit->lit_type == NO_LIT)
    return 1;
  if (lit->bk_type != bk_type)
    return 1;
  if (strcmp(lit->lit_name, lit_name) != 0)
    return 1;
  flag = 0;
  for (j = 1; j <= num_var; j++) {
    bind = binding[j];
    lit_bind = lit->binding[j];
    ot = obj_type[j];
    if (bind == FREE_BINDING) {
      same_index = attr_type[lit_bind] & ot;
      if (same_index == ot)
	matched_num_newvar++;
    }
    else {
      if (bind != lit_bind) {
	flag = 1;
	break;
      }
      else {
	same_index = attr_type[lit_bind] & ot;
	if (same_index != ot)
	  break;
      }
    }
  }
  if (flag || matched_num_newvar < num_newvar)
    return 1;
  return 0;
}

/* sequence number starts at 0  */
int
good_gain (int search_type, double gain, char *lit_name, int binding[], 
	   int obj_type[], int num_var, int num_newvar, int bk_type)
{
  double upper_bound = rule_body_gain[num_rule_lit];
				     
  if ((search_type == ADD_DET_LIT) && (gain != NO_GAIN))
    return 1;
  if (gain < best_gain || gain > upper_bound)
    return 0;

  if (literal_comp (&(rule_literals[num_rule_lit]), lit_name, binding, 
		    obj_type, num_var, num_newvar, bk_type) == 0)
    return 0;
  /* same gain but differnt literals */
  if (gain == upper_bound) {
//   printf (" same gain %f %d, %d\n", gain, bt_seqno, 
//	     rule_lit_seqno[num_rule_lit] + 1);
    if (bt_seqno == rule_lit_seqno[num_rule_lit] + 1) {
      cur_seqno = bt_seqno++;
      return 1;
    }
    bt_seqno++;
    return 0;
  }
  /* first literal with this gain */
  if (gain > best_gain) {
//    printf ("good gain %f\n", gain);
    return 1;
  }
  return 0;
}


/* choose a (un)equality literal */
void
find_equality_literal (void)
{
  int i, j, k;
  int binding[MAX_NUM_PRED_VAR + 1];
  int obj_type[MAX_NUM_PRED_VAR + 1];
  int eq_pos, eq_neg, neq_pos, neq_neg;
  double gain;

  for (i = 1; i < num_attr; i++) {
//      if (ex_literals[i].lit_type == NOT_PRED_LIT)
//          continue;
    for (j = 0; j < i; j++) {    
//      if (ex_literals[j].lit_type == NOT_PRED_LIT)
//          continue;
      if (attr_type[i] == attr_type[j]) {	/* compare composite type */
	eq_pos = eq_neg = neq_pos = neq_neg = 0;
	for (k = 0; k < num_ex; k++) {
	  if (ex_type[k] == NO_EX || (ex_table[k][i] && ex_table[k][j] == 0)) {
	    continue;
	  }
	  if (ex_table[k][i] == ex_table[k][j]) {
	    if (ex_type[k] == 1) 
	      eq_pos++;
	    else
	      eq_neg++;
	  }
	  else {
	    if (ex_type[k] == 1)
	      neq_pos++;
	    else
	      neq_neg++;
	  }
	}
#ifdef BBDEBUG
	printf ("  EQ:[%d][%d] =(%d %d) !=(%d %d) ", i, j, eq_pos, eq_neg, 
		neq_pos, neq_neg);
#endif
	binding[1] = i;
	binding[2] = j;
	obj_type[1] = obj_type[2] = attr_type[i];
	gain = info_gain(eq_pos, eq_neg, eq_pos);
	if (good_gain(FIND_LIT, gain, none_str, binding, obj_type, 2, 
		      0, STATIC)) { 
	  best_lit.lit_name = none_str;
	  best_lit.num_var = 2;
	  best_lit.lit_type = EQUAL_LIT;
	  best_lit.binding[1] = i; 
	  best_lit.binding[2] = j;
	  best_lit.bk_type = STATIC;
	  best_gain = gain;
	  K = eq_pos;
	}
#ifdef BBDEBUG
	printf ("g=%f ", gain);
#endif
	gain = info_gain(neq_pos, neq_neg, neq_pos);
	if (good_gain(FIND_LIT , gain, none_str, binding, obj_type, 2, 
		      0, STATIC)) {
	  best_lit.lit_name = none_str;
	  best_lit.num_var = 2;
	  best_lit.lit_type = UNEQUAL_LIT;
	  best_lit.binding[1] = i; 
	  best_lit.binding[2] = j;
	  best_lit.bk_type = STATIC;
	  best_gain = gain;
	  K= neq_pos;
	}
#ifdef BBDEBUG
	printf ("!g=%f best_gain=%f\n", gain, best_gain);
#endif
      }
    }
  }
}

/* match a predicate p                */
/* return 1: if match; 0: if no match */
int 
match_predicate_literal (int ex, char *p, int binding[], int obj_type[],
			 char *lit_name, int num_var)
{
  char str[100], *s;
  int i, ci, type, ot, same_index;
  
  s = seperate_string(p, str);
  if (strcmp(str, lit_name) != 0)
    return 0;    
  for (i = 1; i <= num_var; i++) {
    s = seperate_string(s, str);
    ci = binding[i];
    if (ci != FREE_BINDING) {
      if (strcmp(str, ex_table[ex][ci]) != 0)
      return 0;
    }
    else {
      find_object_type(str, &type);
      ot = obj_type[i];
      same_index = type & ot;	
      if (same_index != ot) 	/* object is not a supertype of obj_type */
	return 0;
    }
  }
  return 1;
}

/* copy an example from si to di */
void
ex_copy (int si, int di)
{
  ex_type[di] = ex_type[si];
  ex_time[di] = ex_time[si];
  ex_id[di] = ex_id[si];
  for (int i = 0; i < num_attr; i++) 
    ex_table[di][i] = ex_table[si][i];
}

/* update an example by the newly added predicate literal */
void 
update_ex_by_predicate_literal (int ex, char *l, int *binding, int num_var)
{
  char str[100], *s;
  int i, attr_idx, type;
  
  attr_idx = new_num_attr;
  s = seperate_string(l, str);	/* skip predicate name */
  for (i = 1; i <= num_var; i++) {
    s = seperate_string(s, str);
    if (binding[i] == FREE_BINDING) {
      ex_table[ex][attr_idx] = find_object_type(str, &type);
      // attr_type[attr_idx++] |= type;
    }
  }
}

/* update the example table by a predicate literal. the predicate 
   literal could be a determindate literal or a general literal		
   flag = 1: update rule_literals, 0: none, used when backtracking	*/ 
int
update_ex_table_by_predicate_literal (int flag)
{
  int i, j, k, ex, type, num_var, num_newvar, bk_type, *binding, num_added;
  int ex_idx;
  char *lit_name;
  hashtable_t h;
  propspace_ptr ps;
  

  // printf (">> %d\n", num_attr);

  lit_name = best_lit.lit_name;
  binding = best_lit.binding;
  bk_type = best_lit.bk_type;
  num_var = best_lit.num_var;
  ex = num_ex;
  vertex_t v;
  if (flag) {
    obj_type_copy(best_obj_type, &(rule_obj_type[num_rule_lit][0]));
    rule_body_gain[num_rule_lit] = best_gain;
    rule_lit_seqno[num_rule_lit] = cur_seqno;
    for (i = 1; i <= best_lit.num_var; i++)
      best_lit.bind_type[i] = best_lit.binding[i];
    cur_seqno = 0;
    literal_copy(&best_lit, &(rule_literals[num_rule_lit++]));
  }
  
//  printf ("%s [%d][%d], obj_type= %d %d\n", lit_name,
//	  binding[1], binding[2],
//	  best_obj_type[1], best_obj_type[2]); 
  
  
  for (i = 1, num_newvar = 0; i <= best_lit.num_var; i++) {
    if (binding[i] == FREE_BINDING) {
      j = new_num_attr + num_newvar;
      if (j >= MAX_NUM_ATTRIBUTE)
	return -1;
      literal_copy(&best_lit, &(ex_literals[j]));
//      num_attr_type[j] = 1;
      attr_type[j] = best_obj_type[i];
      attr_type_name[j] = 0;
      for (ps = propspaces; ps; ps = ps->next) {
	if (ps->num_var == 1) {
	  for (k = 0; k < ps->num_obj_types; k++) {
	    if (ps->obj_types[k] == attr_type[j]) {
	      attr_type_name[j] = ps->property->item->item;
	      break;
	    }
	  }
	  if (k < ps->num_obj_types)
	    break;
	}
      }
      num_newvar++;
    }
  }
  for (i = 0; i < ex; i++) {
    if (ex_type[i] == NO_EX) {
      for (j = new_num_attr; j < new_num_attr + num_newvar; j++)
	ex_table[i][j] = none_str;
      continue;
    }
    if (bk_type == GOAL) 
      h = goal_table;
    else
      if (bk_type == STATIC)
	h = fact_table[0];
      else {
	h = fact_table[ex_time[i]];
      }
    type = ex_type[i];
    num_added = 0;
    get_next(h, 0);    
    while((v = get_next(h, 1)) != NULL) {
      if (v->is_true == 0)	/* skip false facts */
	continue;
      if (match_predicate_literal(i, v->name, binding, best_obj_type, 
				  lit_name, num_var)) {
	if (num_added == 0)
	  ex_idx = i;
	else {
	  if (num_ex >= MAX_NUM_TABLE_EXAMPLE) {
	    return -1;
//	    do_error("Exceeding maximum number of examples.\n");
	  }
	  ex_idx = num_ex++;
	  ex_copy(i, ex_idx);
	}
	update_ex_by_predicate_literal(ex_idx, v->name, binding, num_var);
	num_added++;
      }
    }
    if (num_added == 0) {
      ex_type[i] = NO_EX;
      for (j = new_num_attr; j < new_num_attr + num_newvar; j++)
	ex_table[i][j] = none_str;
    }
  }
  for (i = new_num_attr; i < new_num_attr + num_newvar; i++) {
    k = 0;
    for (j = 1; j <= best_lit.num_var; j++) {
      ex_literals[i].bind_type[j] = ex_literals[i].binding[j];
      if (ex_literals[i].binding[j] == FREE_BINDING) {
	ex_literals[i].binding[j] = new_num_attr + k;
	k++;
      }
    }
  } 
  new_num_attr += num_newvar;
 
  calculate_ex_table_info_bits();
  /*
  if (num_neg_ex == 0 && flag) {
    literal_copy(&best_lit, &(rule_body[num_rule_body_lit]));
    binding = rule_body[num_rule_body_lit].binding;
    for (i = 1; i <= best_lit.num_var; i++)
      binding[i] = ex_literals[new_num_attr].binding[i];
    num_rule_body_lit++;
  }
  */
  return 1;
}


/* check whether the binding is new or not */
int 
new_binding (char *lit_name, int binding[], int obj_type[], int num_var, 
	     int num_newvar, int bk_type, int mode)
{
  int i;
  literal_ptr lit;
  
  /* check with action precondition literals */
  for (lit = action_precond_literals; lit; lit = lit->next) {
    if (literal_comp(lit, lit_name, binding, obj_type, num_var, num_newvar,
		     bk_type)==0) {
//      printf("Find an action literal\n");
//      print_literal(lit);
      return 0;
    }
  }
  for (i = 1; i <= num_var; i++)
    if (binding[i] == NO_BINDING)	
      return 0;
  /* check with the example table literals */
  for (i = 0; i < new_num_attr; i++) {
    lit = &(ex_literals[i]);
    if (literal_comp(lit, lit_name, binding, obj_type, num_var, num_newvar,
		     bk_type)== 0)
      return 0;
  }
  /* check with the literals in DYNAMIC rule body */
  if (mode == FIND_LIT) {
    for (i = 0; i < num_rule_body_lit; i++) {
      if (literal_comp(&(rule_body[i]), lit_name, binding, obj_type, 
		       num_var, num_newvar, bk_type)== 0) {
	return 0;
      }
    }
  }
  return 1;
}


/* calculate the information gain and return the best		*/
/* Note: negation literal will be only checked when all	        */
/*       variables are old variables. i.e., only positive       */
/*	 literal will be used to introduce new variables	*/
double
predicate_literal_gain (int binding[], int obj_type[], char *lit_name, 
			int num_var, int num_newvar, int bk_type , 
			int mode, int *lit_type)
{
  vertex_t v;
  hashtable_t h;
  int i, num_added, t;
  int pos_included, pos, neg, not_pos, not_neg, not_pos_included;
  double gain, not_gain;

  pos = neg = pos_included = not_pos = not_neg = not_pos_included = 0;
  for (i = 0; i < num_ex; i++) {
    if (ex_type[i] == NO_EX)
      continue;
    if (bk_type == GOAL)
      h = goal_table;
    else
      if (bk_type == STATIC)
	h = fact_table[0];
      else {
	h = fact_table[ex_time[i]];
      }
    get_next(h, 0);
    num_added = -1;
    t = ex_type[i];
    while((v = get_next(h, 1)) != NULL) {
      if (v->is_true == 0)	/* skip false fact */
	continue;
      /*if (strncmp(v->name, "in_", 3) == 0)
       	printf ("%d %s %s %d %d \n", ex_time[i], v->name, lit_name, 
       	obj_type[1], obj_type[2]); */
      if (match_predicate_literal(i, v->name, binding, obj_type, 
				  lit_name, num_var)) {
	if (t == POS_EX) 
	  pos++;
	if (t == NEG_EX) 
	  neg++;
	num_added++;
	if (num_newvar == 0) break;
      }
    }
    if (num_newvar == 0) {	/* for negation literal */
      if (num_added == -1) {
	if (t == POS_EX) 
	  not_pos++;
	else 
	  not_neg++;
      }
   }
    if ((mode == ADD_DET_LIT) && (((num_added > 0) && (t == NEG_EX)) ||
				  ((num_added != 0) && (t == POS_EX))))
      return NO_GAIN;
    if (num_added >= 0 && t == POS_EX)
      pos_included++;
   
    if (num_added == -1 && t == POS_EX)
      not_pos_included++;
  }
  gain = info_gain (pos, neg, pos_included);
  not_gain = (mode >= ADD_DET_LIT) ? NO_GAIN :
    info_gain (not_pos, not_neg, not_pos_included);
#ifdef BBDEBUG  
  printf ("  %s[%d][%d] =(%d %d %d %f) !=(%d %d %d %f) bk=%d\n",
	  lit_name, binding[1], binding[2],
	  pos, neg,  pos_included, gain, 
	  not_pos, not_neg, not_pos_included, not_gain, 
	  bk_type); 
#endif
  if (gain >= not_gain) {
    //if (gain > best_gain)
    //  K = pos_included;
    *lit_type = PRED_LIT;
    return gain;
  }
  else {
    //if (gain > best_gain)
    //  K = pos_included;
    *lit_type = NOT_PRED_LIT;
    return not_gain;
  }
}


/* find the appropriate obj types */
int
find_predicate_literal_obj_type (int binding[],  char *lit_name, 
				 int num_var, int num_newvar, 
				 int bk_type, int search_type)
{
  int i, j, lit_type;
  int universal_type[1];
  int *obj_types[MAX_NUM_PRED_VAR + 1];
  int loop_bound[MAX_NUM_PRED_VAR + 1], loop[MAX_NUM_PRED_VAR + 1];
  int obj_type[MAX_NUM_PRED_VAR + 1];
  propspace_ptr ps;
  double gain;

  universal_type[0] = UNIVERSAL_TYPE;
  for (i = 1; i <= num_var; i++) {
    if (binding[i] == NO_BINDING)
      return 1;
    if (binding[i] == FREE_BINDING) {
      ps = find_property_space(lit_name, i);
      ps = ps->root;
      loop_bound[i] = ps->num_obj_types;
      if (loop_bound[i] == 0) {		// no type
	loop_bound[i] = 1;
	obj_types[i] = universal_type;
      }
      else 
	obj_types[i] = ps->obj_types;
    }	
    else {
      loop_bound[i] = 1;
      obj_types[i] = (int *)&(attr_type[binding[i]]);
    }
    obj_type[i] = obj_types[i][0];
    loop[i] = 1;
  }
  /*
  for (i = 1; i <= num_var; i++)
    printf(" (%d)", binding[i]);
  printf("\n");
  for (i = 1; i <= num_var; i++)
    printf(" [%d]", loop_bound[i]);
  printf("\n"); */
  loop_bound[0] = 1;
  loop[0] = 0; 		/* boundary condition for loop */
  for (i = num_var; ; ) {
    if (new_binding(lit_name, binding, obj_type, num_var, num_newvar, bk_type, 
		    search_type)) { 
      //printf ("obj_type: %d %d\n", obj_type[1], obj_type[2]);
      gain = predicate_literal_gain(binding, obj_type, lit_name, num_var, 
				    num_newvar, bk_type, search_type, 
				    &lit_type);
      if (good_gain(search_type, gain, lit_name, binding, obj_type, num_var, 
		    num_newvar, bk_type)) {
	best_lit.lit_name = lit_name;
	best_lit.lit_type = lit_type;
	// printf ("find a new object %s %d\n", lit_name, bk_type);
	best_lit.bk_type = bk_type;
	best_lit.num_var = num_var;
	for (j = 1; j <= num_var; j++) {
	  best_lit.binding[j] = binding[j];
	  best_obj_type[j] = obj_type[j];
	}
	// printf ("obj_type %d %d\n", obj_type[1], obj_type[2]);
	if (search_type == ADD_DET_LIT) {
	  best_lit.rule_lit_type = ADD_DET_LIT;
	  if (update_ex_table_by_predicate_literal(1) == -1) {
	    //printf("%d %d \n", num_attr, new_num_attr);
	    return -1;
	  }
#ifdef BBDEBUG
	  if (search_type == ADD_DET_LIT) {
	    printf ("==> Add determinate literal: %s[%d][%d]\n", lit_name, 
		    binding[1], binding[2]);
	  }
	  else
	    printf ("Adding literal: %s[%d][%d]\n", lit_name, 
		    binding[1], binding[2]);
#endif

	}
	best_gain = gain;
      }
      /*
      printf ("%s ", lit_name);
      for (j = 1; j <= num_var; j++)
	printf(" [%d]", obj_type[j]);
      printf("\n");  */
    }
    /*
    for (j = 1; j <= 3; j++)
      printf (" %d", loop[j]);
    printf ("\n"); */
    while (loop[i] == loop_bound[i]) {
      loop[i] = 1;
      obj_type[i] = obj_types[i][0];
      i--;
    }
    if (i == 0)
      break;
    loop[i]++;
    // printf ("..... %d %d\n", loop[i], i);
    obj_type[i] = obj_types[i][loop[i] - 1];
    i = num_var;
  }
  return 1;
}

/* find the best binding for a predicate literal */
int
find_predicate_literal_binding (int var_type[], char *lit_name, int loc,
				int num_var, int attr, int num_newvar, 
				int bk_type, int search_type)
{
  int j, k, loop_flag, binding_changed;
  propspace_ptr psi;
  int loop[MAX_NUM_PRED_VAR + 1], binding[MAX_NUM_PRED_VAR + 1];
  
  for (j = 1; j <= num_var; j++) {	/* initalize loop */
    loop[j] = 0;	
    binding[j] = NO_BINDING;		/* no binding */
  }		
  binding_changed = 0;
  for (loop_flag = j = 1; loop_flag; ) { 	
    if (var_type[j] == NEW_VAR)		/* location for the new variable */
      binding[j] = FREE_BINDING;
    else
      if (j == loc) {
	binding_changed = 1;
	binding[j] = attr;
      }
      else {
	if (j <= num_var) {
	  while (loop[j] < num_attr) {
	    k = loop[j]++;
	    if (k == attr) break;
	    if ((psi = find_property_space(lit_name, j))) {
	      psi = psi->root;
	      if (psi->index & attr_type[k]) {
		binding_changed = 1;
		binding[j] = k;
		break;
	      }
	    }
	  }
	}
      }
    j++;
    /* printf ("%d [%d][%d]\n", j, binding[1], binding[2]);
    printf ("loop [%d][%d] ", loop[1], loop[2]);
    printf ("%d %d %d\n", j, loop[j], num_attr); */
    if (j > num_var) {
      /* good binding */
      if (binding_changed) {
	binding_changed = 0;
      /* printf ("$$ %s loc = %d v = %d attr = %d #nv = %d\n", 
		  lit_name, loc, num_var, attr, num_newvar); */
	if (find_predicate_literal_obj_type (binding, lit_name, num_var,
	    num_newvar, bk_type, search_type) == -1)
	  return -1;
      }
      j--;
      while(loop[j] == num_attr || j == loc || var_type[j] == NEW_VAR) {
	if (j == 1) {
	  loop_flag = 0;
	  break;
	}
        binding[j] = NO_BINDING;
	loop[j--] = 0;
      }
    }
  }
  return 1;
}

/* enumerate possible predicate literal by the number of new variables */
int
find_add_predicate_literal (char *lit_name, int loc, int num_var, int attr, 
			    int num_newvar, int bk_type, int search_type)
{	
  int i, j, k, n, cp;
  int loop_flag, prev_num_attr;
  int var_type[MAX_NUM_PRED_VAR + 1];
   
  //printf (">>%s %d %d %d b = %d\n", lit_name, loc, num_var, attr, bk_type);
  /* enumerate possible new variables combinations */
  prev_num_attr = num_attr;
  for (i = (search_type >= ADD_DET_LIT) ? 1 : 0; i <= num_newvar; i++) {
    /* initialize variable type array */
    var_type[0] = OLD_VAR;		/* array boundary */
    for (j = 1; j <= num_var; j++) 
      var_type[j] = (j <= i) ? NEW_VAR : OLD_VAR;
    for (cp = i, loop_flag = 1; loop_flag; ) {
      if (var_type[loc] != NEW_VAR) {
	//printf ("%s ", lit_name);
	//for (k = 1; k <= num_var; k++)
	//printf("[%d]", var_type[k]);
	//printf("\n");
	if (find_predicate_literal_binding(var_type, lit_name, loc, num_var, 
             attr, i, bk_type, search_type) == -1)
	  return -1;
	if ((search_type == ADD_NEWVAR_LIT) && (prev_num_attr != new_num_attr))
	  return 1;
      }
      if (i == 0)
	break;
      if (cp == num_var) {
	for (j = num_var; var_type[j] == NEW_VAR; j--);
	n = num_var - j; 
	if (n == i) {
	  loop_flag = 0;
	}
	for (; var_type[j] == OLD_VAR && j >= 0; j--);
	var_type[j++] = OLD_VAR;
	for (k = 0; j <= num_var; j++, k++) {
          var_type[j] = (k <= n) ? NEW_VAR : OLD_VAR;
	  if (k == n) cp = j;
	}
      } 
      else {
	var_type[cp++] = OLD_VAR;
	var_type[cp] = NEW_VAR;
      }
    }
  }
  return 1;
}

/* match the predicate literal and background knowledge type 	*/
/* used for adding determinate varialbes 			*/
int 
match_literal_and_type (propspace_ptr ps, int bk_type, int search_type)
{
  int type;
  char *lit_name = ps->property->item->item;

  /*  type = ATTRIBUTE;
  propspace_ptr p;
  for (i = 1; i <= ps->num_var; i++) {
    p = find_property_space(ps->property->item->item, i);
    p = p->root;
    if (p->type == PROPERTY) {
      type = PROPERTY;
      break;
    }
  } */
  if ((search_type == FIND_LIT) && (bk_type == DYNAMIC))
    return 0;
  type = find_predicate_type(lit_name);
  if ((type == STATIC) && (bk_type != STATIC))
    return 0;
  if ((type == DYNAMIC) && (bk_type == STATIC))
    return 0; 
  return 1;
}

/* fidn a best predicate literal */
int
search_predicate_literal (int search_type)
{
  int i, loc, bk_type, num_var, num_new_var, prev_num_attr;
  propspace_ptr ps;
  token_list token;

  num_new_var = (search_type == FIND_LIT) ? 0 : 1;
  prev_num_attr = num_attr;

//  printf ("num_attr = %d, num_new_var = %d \n", num_attr, num_new_var);
  for (bk_type = (phase == STATIC) ? STATIC : DYNAMIC; 
       bk_type <= GOAL; bk_type++) {
    for (i = 0; i < num_attr; i++) {
      for (ps = propspaces; ps; ps = ps->next) {
	if (ps->root->index & attr_type[i]) {
//	  print_fact_list (ps->property);
//	  printf ("## %d %d \n", attr_type[i], i);
	  if (!match_literal_and_type(ps, bk_type, search_type))
	    continue;
//	  printf ("OK here\n");
	  token = ps->property->item;
	  num_var = ps->num_var;
	  if (search_type == ADD_NEWVAR_LIT)
	    num_new_var = num_var - 1;
	  loc = atoi(token->next->item);
	  if (find_add_predicate_literal(token->item, loc, num_var, i,
              num_new_var, bk_type, search_type) == -1)
	    return -1;
	}
      }
    }
  }
  return 1;
}

/* update example table types */
void
update_ex_table_type_by_predicate ()
{
  int i, num_var, bk_type, *binding, num_added;
  int type, lit_type;
  char *lit_name;
  vertex_t v;
  hashtable_t h;

  lit_name = best_lit.lit_name;
  lit_type = best_lit.lit_type;
  num_var = best_lit.num_var;
  bk_type = best_lit.bk_type;
  binding = best_lit.binding;
  for (i = 0; i < num_ex; i++) {
    if (ex_type[i] == NO_EX)
      continue;
    if (bk_type == GOAL) 
      h = goal_table;
    else
      if (bk_type == STATIC)
	h = fact_table[0];
      else
	h = fact_table[ex_time[i]];
    
    type = ex_type[i];
    num_added = 0;
    get_next(h, 0);    
    while((v = get_next(h, 1)) != NULL) {
      if (match_predicate_literal(i, v->name, binding, best_obj_type, 
				  lit_name, num_var)) {
	num_added++;
	break;
      }     
    }
    if (num_added) {
      if (lit_type == NOT_PRED_LIT)
	ex_type[i] = NO_EX;
    }
    else
      if (lit_type == PRED_LIT)
	ex_type[i] = NO_EX;
  }
}

/* update the example table type by equality literal */
void
update_ex_table_type_by_equality ()
{
  int ex, lit_type, a1, a2;
  lit_type = best_lit.lit_type;
  a1 = best_lit.binding[1];
  a2 = best_lit.binding[2];

  if (lit_type == EQUAL_LIT) {
    for (ex = 0; ex < num_ex; ex++)
      if (ex_table[ex][a1] != ex_table[ex][a2]) ex_type[ex] = NO_EX;
  }
  else {
    for (ex = 0; ex < num_ex; ex++)
      if (ex_table[ex][a1] == ex_table[ex][a2]) ex_type[ex] = NO_EX;
  }
}

/* update the example table type */
void
update_ex_table_type ()
{
  int lit_type = best_lit.lit_type;
  if ((lit_type == PRED_LIT) || (lit_type == NOT_PRED_LIT))
    update_ex_table_type_by_predicate();
  if ((lit_type == EQUAL_LIT) || (lit_type == UNEQUAL_LIT))
    update_ex_table_type_by_equality();
  // update up constant ?
}
 
/* check whether the literal is good enough (and upate the best literal) */ 
int
good_literal ()
{	
  switch (gain_heuristics) {
  case 1:	
    if (best_gain > ex_table_info_bits) return 1;
    break;
  case 2:
    if (best_gain == 0.0) return 1;
    break;
  case 3:
    if (best_gain*K >= num_pos_ex * ex_table_info_bits * GAIN_FACTOR)
    return 1; 
  }
  return 0;
}


/* add the best literal found to rule body */
void
add_literal2rule ()
{
  int i;

  for (i = 1; i <= best_lit.num_var; i++)
    best_lit.bind_type[i] = best_lit.binding[i];
  best_lit.rule_lit_type = -1;
  literal_copy(&best_lit, &rule_body[num_rule_body_lit]);
  rule_lit_seqno[num_rule_lit] = cur_seqno;
  cur_seqno = bt_seqno = 0;
  rule_body_gain[num_rule_lit] = best_gain;
  literal_copy(&best_lit, &rule_literals[num_rule_lit++]);
  num_rule_body_lit++;
  //  new_lit->prev_num_ex = num_ex;
  /* update example table after new literal! */
  update_ex_table_type();
  calculate_ex_table_info_bits(); 
  /* add literal into rule_body */
  /*
  if (rule_body == NULL)
    rule_body = new_lit;
  else {
    for (lit_tmp = rule_body; lit_tmp->next; lit_tmp = lit_tmp->next);
    lit_tmp->next = new_lit;
  }
  */
#ifdef BBDEBUG
  print_ex_table();
  printf ("best_gain = %f ex_tab = %f\n", best_gain, ex_table_info_bits);
  printf ("pos_ex: %d, neg_ex: %d\n", num_pos_ex, num_neg_ex);
#endif
}

/*
void
build_rule ()
{
  learned_rule_ptr r;

  r = (learned_rule_ptr)calloc(1, sizeof(learned_rule_elt));
  r->body = rule_body;
  if (learned_rules != NULL)
    r->next = learned_rules;
  learned_rules = r;
}
*/

/* find a literal that can be added to the rule body 	      	*/
/* A literal can be a predicate P(X1,...Xk), not P(X1,...Xk), 	*/
/*   Xi = Xj, Xi != Xj, Xi = c, or Xi != c                     	*/
/* find_constant_literal() is not implemented yet		*/
int 
find_literal ()
{ 
  best_gain = NO_GAIN;
  find_equality_literal();
  search_predicate_literal(FIND_LIT);
  // find_constant_literal ();
  if (good_literal()) {
#ifdef BBDEBUG
    printf ("==> find a literal: %s[%d][%d] lit_type=%d bk=%d \n", 
	    best_lit.lit_name, best_lit.binding[1], best_lit.binding[2],
	    best_lit.lit_type, best_lit.bk_type);
#endif
    add_literal2rule();
    return 1;
  }
  return 0;
}

/* add determinate literals */
int
add_determinate_literals () 
{
  int prev_num_attr = num_attr;
  new_num_attr = num_attr;
  // best_gain = NO_GAIN;
  if (search_predicate_literal(ADD_DET_LIT) == -1)
    return -1;
  num_attr = new_num_attr;
  return ((num_attr != prev_num_attr) ? 1 : 0);
}

/* add the literal with the highest positive gain */
int
add_positive_gain_literal ()
{
  int lit_type = best_lit.lit_type;

  switch (gain_heuristics) {
  case 1:
  case 2:
    if (best_gain <= ex_table_info_bits) /* must be <= */
      return 0;
  case 3:
    if (best_gain <= 0.0)
      return 0;
  }
#ifdef BBDEBUG
  printf ("==> Add positvie gain literal: ");
  if (lit_type <= NOT_PRED_LIT)
    printf ("  %s bk = %d ", best_lit.lit_name, best_lit.bk_type);
  printf ("lit_type = %d [%d][%d]\n", lit_type,
	  best_lit.binding[1], best_lit.binding[2]);
#endif
  add_literal2rule();
  return 1;
}

/* add the literal introducing new variables with 
   the higest information gain 				*/
int
add_new_variable_literal ()
{
  best_gain = NO_GAIN;
  new_num_attr = num_attr;
  search_predicate_literal(ADD_NEWVAR_LIT);
  if (best_gain <= NO_GAIN)
    return 0;
  best_lit.rule_lit_type = ADD_NEWVAR_LIT;
  if (update_ex_table_by_predicate_literal(1) == -1)
    return -1;
  num_attr = new_num_attr;
#ifdef BBDEBUG
  printf ("Add new variable literal: ");
  printf ("%s[%d][%d] bk=%d lit_type=%d\n", best_lit.lit_name, 
	  best_lit.binding[1], best_lit.binding[2], 
	  best_lit.bk_type, best_lit.lit_type);
  print_ex_table();
#endif
  return 1;
}

/* mode = 1: make node covered by rule 
          2: backtracking mode        	 */
void
reset_ex_type (int mode)
{
  int i, id;

  if (mode != 2) {
    for (i = 0; i < num_ex; i++) {
      if (ex_type[i] == POS_EX) {
	id = ex_id[i];
	ex_type_backup[id] = NO_EX;
	if (mode && ex_node[id]->used == 0) 
	  ex_node[id]->is_true = NODE_COVERED;
      }
    }
  }
  num_ex = orig_num_ex;
  for (i = 0; i < num_ex; i++) {
    ex_type[i] = ex_type_backup[i];
  }
  num_attr = orig_num_attr;
}

void
reset_rule_body ()
{
  num_rule_lit = num_rule_body_lit = cur_seqno = 0;
  for (int i = 0; i < MAX_NUM_RULE_BODY_LITERAL+MAX_NUM_ATTRIBUTE; i++) {
    rule_body_gain[i] = MAX_GAIN;
    rule_lit_seqno[i] = 0;
  }
}

/* check whether the literal introduces a new variable or not 	
   return 1: yes, 0: no 					*/
int
new_variable (literal_ptr lit)
{
  int *b = lit->binding;
  for (int i = 1; i <= lit->num_var; i++) {
    if (b[i] == FREE_BINDING)
      return 1;
  }
  return 0;
}


/* perform limited rule backtracking */
int
rule_backtracking ()
{
  int i;

  if (learn_bt_flag == 0) {
    return 0;
  }
//  printf("%d %d\n", num_rule_body_lit, num_rule_lit);
//  for (i = 0; i < num_rule_lit; i++) 
//    printf("[%d] %f\n", rule_literals[i].rule_lit_type,
//	   rule_body_gain[i] );  
  num_rule_lit--;
  if (new_variable(&(rule_literals[num_rule_lit])) == 0) 
      num_rule_body_lit--;
  while (num_rule_lit >= 0 && 
	 (rule_literals[num_rule_lit].rule_lit_type == ADD_DET_LIT ||
	  rule_body_gain[num_rule_lit] <= 0.0)) {
    rule_body_gain[num_rule_lit] = MAX_GAIN;
    num_rule_lit--;
    if (new_variable(&(rule_literals[num_rule_lit])) == 0) 
      num_rule_body_lit--;
  }

  if (num_rule_lit < 0) 
    return 0;
//  printf("\n%d %d %f\n", num_rule_body_lit, num_rule_lit,
//	 rule_body_gain[num_rule_lit]);
  reset_ex_type(2);
//  printf ("Backtracking\n");
  for (i = 0; i < num_rule_lit; i++) {
    literal_copy(&(rule_literals[i]), &best_lit);
    if (new_variable(&(rule_literals[i]))) {
      obj_type_copy(rule_obj_type[i], best_obj_type);
      new_num_attr = num_attr;
      update_ex_table_by_predicate_literal(0);	
      num_attr = new_num_attr;
    }
    else
      update_ex_table_type ();
//    print_literal (&(rule_literals[i]));
//    print_ex_table();
  }
  calculate_ex_table_info_bits();
//  print_ex_table();
//  printf ("*****************************************************\n");
  cur_seqno = bt_seqno = 0;
  return 1;
}

/* learn rules for an action */
void 
learn_action_rule (int rule_type)
{
  int loop_flag, rule_flag, done, bt_flag;
  
  reset_ex_type(0);
  calculate_ex_table_info_bits();
  reset_rule_body();
  if (num_neg_ex == 0 && num_pos_ex > 0) {
    if (phase == STATIC && rule_type == 1) {
#ifdef BBDEBUG
      print_rule();
      printf("=======================================\n");
#endif      
      verify_rule(1);
    }
    return;
  }
  done = 1;
  bt_flag = 0;
  for (loop_flag = 1; loop_flag; ) {
#ifdef BBDEBUG
    print_ex_table();
#endif
    if (bt_flag == 0) {
      rule_flag = 0;
      reset_rule_body();
    }
    if (num_pos_ex == 0) {
      loop_flag = 0;
      continue;
    }
    while (num_neg_ex && loop_flag) {
      if (done == -1) {
	return;
      }

#ifdef BBDEBUG
      printf ("<<< Find maximum gain literals >>>\n");
#endif
      
      if (num_rule_body_lit < MAX_NUM_RULE_BODY_LITERAL && find_literal()) {
#ifdef BBDEBUG
      printf ("(%d %d): gain = %f, info_bits = %f\n", num_pos_ex, num_neg_ex, 
	      num_pos_ex * ex_table_info_bits, ex_table_info_bits);
      printf ("<<< Find a literal with greatest gain >>>\n");
#endif
	continue;
      }
#ifdef BBDEBUG
      printf ("<<< Add determindate literals >>>\n");
#endif
      if ((done = add_determinate_literals())) {
#ifdef BBDEBUG
	print_ex_table();
#endif
	continue;
      }
#ifdef BBDEBUG
      printf ("<<< Add positive literal >>>\n");
#endif
      if (num_rule_body_lit < MAX_NUM_RULE_BODY_LITERAL && 
	  add_positive_gain_literal()) {
	continue;
      }
#ifdef BBDEBUG
      printf ("<<< Add new variable literal >>>\n");
#endif
      if ((done = add_new_variable_literal()))
	continue; 
      loop_flag = 0;
    }
    if (done == -1) {
      if (rule_backtracking()) {
	bt_flag = loop_flag = 1;
	continue;
      }
      return;
    }
    if ((num_rule_body_lit > 0) || 
	((phase == DYNAMIC) && (rule_type == -1))) {
#ifdef BBDEBUG
      print_rule();
     print_backup_rule();      
#endif
      if (learn_bt_flag == 0) {
	verify_rule(rule_type);
	rule_flag = 1;
      }
      else {
//          printf ("veryfing\n");
//          
          if (verify_rule(rule_type)) {
              rule_flag = 1;
          }	
          else {
              
              if (rule_backtracking()) {
                  bt_flag = loop_flag = 1;
                  continue;
              }
          }
      }
    }
    bt_flag = 0;
    reset_ex_type(rule_flag);
    calculate_ex_table_info_bits();
  }
}

/* initalize examples types	*/
void
init_ex_type (int rule_type){
  int i, type;

  num_ex = orig_num_ex;
  for (i = 0; i < num_ex; i++) {
    ex_type[i] = NO_EX;
    if (rule_type == 1)		/* learning rules for positive examples */
      type = (ex_node[i]->used == 1) ? POS_EX : NEG_EX;
    else 
      type = (ex_node[i]->used == 1) ? NEG_EX : POS_EX;
    ex_type_backup[i] = type;
  }
}

void 
learn_action_rules()
{
#ifdef BBDEBUG
  printf("learning positive rules\n");
#endif
  init_ex_table ();
  collect_examples(1);
//  printf ("s: %d ", orig_num_ex);
  init_ex_type (1);
  learn_action_rule (1);	/* learn rules for positive examples */
#ifdef BBDEBUG
  printf("learning negative rules\n");
#endif
  init_ex_table ();
  collect_examples(-1);
//  printf ("d: %d\n", orig_num_ex);
  init_ex_type(-1);
//  print_ex_table(); 
  learn_action_rule (-1);	/* learn rules for negative examples */
}

void 
learn () 
{ 
//  dummy_literal.lit_name = none_str;
  elapsed_seconds();
  for (cur_op = ops; cur_op; cur_op = cur_op->next) {
#ifdef BBDEBUG
    fprintf(STDMSG, "learning rules for aciton: %s\n", cur_op->name);
#endif
//  if (strcmp(cur_op->name, "jack-down") != 0)
//      continue;

//    printf ("%s\n", cur_op->name);  
    learned_rules = 0;
    init_action_ex_literals();
//    print_action_literals();
//    fprintf(STDMSG, "learning static rules\n");
    phase = STATIC;
    learn_action_rules();
//    fprintf(STDMSG, "learning dynamic rules\n");    
    phase = DYNAMIC;
    learn_action_rules();
    free_action_literals();
  }
  fprintf(STDMSG, "Control rules are learned in %.2f seconds\n", 
	  elapsed_seconds());
}

#endif

