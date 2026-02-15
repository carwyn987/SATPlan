/****************************************************************/
/* verify.c							*/
/****************************************************************/

#ifdef BBLEARN

#define BBDEBUG

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

extern op_list ops;
extern defpred_list dps;
extern control_list controls;
extern wffctrl_list wffctrls;
extern int global_maxtime;
extern hashtable_t *fact_table, *op_table, goal_table;
extern int learn_mode;
extern char *exists_str;

int num_rule;
int rule_value;
int rule_pruned;
int rule_evaluated;
int remove_dummy_flag = 1;
wffctrl_list current_control = 0;
fact_list current_precond = 0;


void 
free_graph_control (control_list c)
{
  free(c->name);
  completely_free_fact_list(c->excludes);
  free(c);
}

void
free_graph_controls ()
{
  control_list tmp, c = controls;
  while (c) {
    tmp = c->next;
    free_graph_control(c);
    c = tmp;
  }
  controls = 0;
}

void 
free_wff_control (wffctrl_list c)
{
  c->last_scope->next = 0;	/* remember to restore the connector */
  free(c->name); 
  completely_free_fact_list(c->scope);
  completely_free_fact_list(c->preconds);
  completely_free_fact_list(c->effects);
  free(c);
}

void
free_wff_controls ()
{
  wffctrl_list tmp, c = wffctrls;
  while (c) {
    tmp = c->next;
    free_wff_control(c);
    c = tmp;
  }
  wffctrls = 0;
}

op_list
find_action (char *action_name)
{
  op_list a;

  for (a = ops; a; a = a->next) {
    if (strcmp(a->name, action_name) == 0)
      return a;
  }
}

instantiation_list 
build_action_instantiation (op_list a, char *s)
{
  instantiation_list inst_list = 0, inew;
  fact_list param;
  char str[50];
  int dummy;

  param = a->params;
  while (s) {
    s = seperate_string(s, str);
    inew = (instantiation_list)calloc(1, sizeof(instantiation_s));
    inew->var_part = param->item->item; 	
    inew->const_part = find_object_type(str, &dummy);
    if (inst_list)
      inew->next = inst_list;
    inst_list = inew;
    param = param->next;
  }
  return inst_list;
}


int
mark_node_covered_by_graph_control (char *n, instantiation_list insts, int t)
{
  for (control_list ctrl = controls; ctrl; ctrl = ctrl->next) {
    if (strcmp(n, ctrl->name) == 0) {
      if (eval (ctrl->excludes, insts, t))
	return 1;
    }
  }
  return 0;
}

int
mark_node_covered_by_wff_control (char *n, instantiation_list insts, int t)
{ 
  
  
  for (wffctrl_list ctrl = wffctrls; ctrl; ctrl = ctrl->next) {
    rule_evaluated = 0;
    current_control = ctrl;
    current_precond = ctrl->preconds;
    if (strcmp(n, ctrl->name) == 0) {
//      printf("time = %d\n", t);
//      print_instantiation(insts);
      eval(ctrl->scope, insts, t);
      if (rule_evaluated)
	return 1;
    }
  }
  current_control = 0;
  current_precond = 0;
  return 0;
}

/* mark nodes covered by rules */
void
mark_node_covered_by_rule ()
{
  int i;
//  int num_covered_node = 0;
  char str[50], *s;
  vertex_t v;
  op_list a;
  instantiation_list insts;

  for (i = 0; i < global_maxtime; i++) {
    get_next(op_table[i],0);
    while((v = get_next(op_table[i], 1)) != NULL) {
      if (IS_NOOP(v))
	continue;
      s = seperate_string(v->name, str);
      a = find_action(str);
      insts = build_action_instantiation(a, s);
      if (((v->used == 0) && mark_node_covered_by_graph_control(str,insts,i)) 
	  || mark_node_covered_by_wff_control(str, insts, i)) {
//	num_covered_node++;
//	printf("  node:%s at time %d is covered!\n", v->name, i);
	v->is_true = NODE_COVERED;
      }
      free_instantiation (insts);
    }
  }
//  fprintf(STDMSG, "    %d nodes are covered by rules\n", num_covered_node);
}


/* parameters: name: action name; inst: action instantiation; t: time */
void 
verify_graph_control (char *name, instantiation_list insts, int t)
{
  control_list ctrl, prev_ctrl, tmp_ctrl;

  ctrl = controls;
  while(ctrl) {
    if ((strcmp(ctrl->name, name) == 0) && eval (ctrl->excludes, insts, t)) {
      rule_pruned++;
      tmp_ctrl = ctrl;
      if (ctrl == controls)
	controls = ctrl = ctrl->next;
      else
	prev_ctrl->next = ctrl = ctrl->next;
      free_graph_control(tmp_ctrl);
    }
    else {
      prev_ctrl = ctrl;
      ctrl = ctrl->next;
    }
  }
}

fact_list
find_last_fact (fact_list fact)
{
  char *str;
  
  while (1) {
    str = fact->item->item;
    if ((strcmp(str, "forall") == 0) || (strcmp(str, "exists") == 0))
      fact = fact->body;
    else {
      if (fact->next == NULL)
	return fact;
      fact = fact->next;
    }
  }
}

/* find the last fact in the scope and preconditions */
void
setup_wff_control_connector ()
{
  for (wffctrl_list ctrl = wffctrls; ctrl; ctrl = ctrl->next) {
    ctrl->last_scope = find_last_fact(ctrl->scope);
    //ctrl->last_precond = find_last_fact(ctrl->preconds);
    ctrl->last_scope->next = ctrl->preconds;
    //ctrl->last_precond->next = ctrl->effects;
  }   
}


/* restore the last fact in the scope and preconditions */
void 
restore_wff_control_connector ()
{
  for (wffctrl_list ctrl = wffctrls; ctrl; ctrl = ctrl->next)
    ctrl->last_scope->next = 0;
}


/* and remove dummy rules 				*/
void
remove_dummy_rule (int mark_node)
{
  wffctrl_list ctrl, prev_ctrl, tmp_ctrl;

  if (mark_node)	/* don't remove previous learned dummy rules */
    return;
  if (remove_dummy_flag == 0)
    return;
  ctrl = wffctrls; 
  while (ctrl) {
    if (ctrl->is_used == 0) {
      rule_pruned++;
      tmp_ctrl = ctrl;
      if (ctrl == wffctrls)
	wffctrls = ctrl = ctrl->next;
      else
	prev_ctrl->next = ctrl = ctrl->next;
      /* free_ctontrol (tmp_ctrl); */
    }
    else {
      prev_ctrl = ctrl;
      ctrl = ctrl->next;
    }
  } 
}

/*
void 
verify_wff_control (char *name, instantiation_list insts, int t)
{
  wffctrl_list ctrl, prev_ctrl, tmp_ctrl;

  ctrl = wffctrls;
  while(ctrl) {
    if (strcmp(ctrl->name, name) == 0) {
      rule_value = 1;
      current_control = ctrl;
      current_precond = ctrl->preconds;
      eval (ctrl->scope, insts, t);
      if (rule_value == 0) {
	rule_pruned++;
	tmp_ctrl = ctrl;
	if (ctrl == wffctrls)
	  wffctrls = ctrl = ctrl->next;
	else
	  prev_ctrl->next = ctrl = ctrl->next;
	continue;
      }
    }
    prev_ctrl = ctrl;
    ctrl = ctrl->next;
  }
  current_precond = 0;
  current_control = 0;
}
*/


void 
verify_wff_control (int t)
{
  wffctrl_list ctrl, prev_ctrl, tmp_ctrl;

  ctrl = wffctrls;
  while(ctrl) {
    rule_value = 1;
    current_control = ctrl;
    current_precond = ctrl->preconds;
    eval (ctrl->scope, NULL, t);
    if (rule_value == 0) {
      rule_pruned++;
      tmp_ctrl = ctrl;
      if (ctrl == wffctrls)
	wffctrls = ctrl = ctrl->next;
      else
	prev_ctrl->next = ctrl = ctrl->next;
      free_wff_control(tmp_ctrl);
    }
    else {
      prev_ctrl = ctrl;
      ctrl = ctrl->next;
    }
  }
  current_precond = 0;
  current_control = 0;
}

int
verify_rules (int mark_node)
{
  int i;
  char str[50], *s;
  vertex_t v;
  op_list a;
  instantiation_list insts;

  setup_wff_control_connector();
  for (i = 0; i < global_maxtime; i++) {
    get_next(op_table[i],0);
    while((v = get_next(op_table[i], 1)) != NULL) {
      if (!v->used || IS_NOOP(v))
	continue;
      s = seperate_string(v->name, str);
      a = find_action(str);
      insts = build_action_instantiation(a, s);
      verify_graph_control(str, insts, i);
//      verify_wff_control (str, insts, i);
      free_instantiation (insts);
    }
    verify_wff_control(i);
  }
  remove_dummy_rule(mark_node);
//  if (mark_node && (learn_mode & LEARN_CONTROL))
    mark_node_covered_by_rule ();
  restore_wff_control_connector();
  num_rule = 0;
  i = (controls == 0 && wffctrls == 0) ? 0 : 1;
  print_verified_rules();
  free_graph_controls();
  free_wff_controls();
  return i;
}

/* verify a single rule 			
   return 1: if the rule is consistant; the rule is also printed out
          0: if the rule is not correct or a dummy rule         	*/
int
verify_rule (int rule_type)
{
  load_rule(rule_type);
  return verify_rules(0);
}

/* main routin for verifying a set of control rules 	*/
void
verify (int mark_node) 
{
  rule_pruned = 0;
  fprintf(STDMSG, "Verifying control rules: \n");
  elapsed_seconds();
  verify_rules(mark_node);
  fprintf(STDMSG, "    %d rules are discarded in %.2f seconds\n", 
	  rule_pruned, elapsed_seconds());
  fprintf(STDMSG, "    %d rules are correct\n", num_rule);  
}

#endif
