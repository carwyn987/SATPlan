#include <stdlib.h>
#include <string.h>
#include "utilities.h"
#include "control.h"

extern fact_list initial_facts, the_goals, the_types;
extern hashtable_t *fact_table, *op_table; 
extern hashtable_t goal_table;

#ifdef BBLEARN
extern wffctrl_list current_control;
extern fact_list current_precond;
extern int rule_value, rule_evaluated;
#endif

defpred_list dps = NULL;
control_list controls = NULL;
wffctrl_list wffctrls = NULL;

/* generate candidates satisfying condition for exists & forall
 * return: a token list of candidates
 * notes: the caller needs to free the memory 
 */ 
token_list make_generator(token_list param, token_list condition, 
			  instantiation_list insts, int time)
{
  int found;
  char *candidate, *str2;
  fact_list fact;
  token_list head, cur, t1, t2;

  head = cur = NULL;

  if (strcmp(condition->item, "goal") == 0) {	
    condition = condition->next;
    fact = the_goals;
  }
  else
    if (strcmp(condition->item, "true") == 0) {
      for (fact = the_types; fact; fact = fact->next) {
	t1 = strdup2token(fact->item->item);
	if (head == NULL)	
	  head = cur = t1;
	else
	  cur = cur->next = t1;
      }
      return head;
    }
    else {
      fact = initial_facts;
      // fact = make_list_from_htable(fact_table[time]);
    }
 

  for (fact; fact; fact = fact->next) {
    found = 1;
    for (t1 = fact->item, t2 = condition; t1 && t2; 
	 t1 = t1->next, t2 = t2->next) {
      str2 = t2->item;
      if (is_var(str2)) {
	if (strcmp(param->item, str2) == 0) {
	  candidate = t1->item;      	/* possible candidate */
	  continue;
	}
	else { 		     		/* check instantiation */ 
	  str2 = lookup_instantiation(insts, str2);
	}
      }
      if (strcmp(t1->item, str2) != 0) {
	found = 0;
	break;
      }
    }
    if (found && t1 == t2) {	     	/* add candidate to list */
      t1 = strdup2token(candidate);
      if (head == NULL)	
	head = cur = t1;
      else
	cur = cur->next = t1;
    }
  }
    
  return head;
}

defpred_list 
lookup_defpred (char *str)
{
  defpred_list dp;
  
  for (dp = dps; dp; dp = dp->next) {
    if (strcmp(str, dp->name) == 0)
      return dp;
  }
  return NULL;
}

instantiation_list 
setup_defpred_instantiation (defpred_list dp, token_list token,
			     instantiation_list insts)
{
  instantiation_list inst, inext, inew;
  fact_list param;
  
  inst = NULL;
  for (param = dp->params; param && token; 
       param = param->next, token = token->next) {
    inew = (instantiation_list)calloc(1, sizeof(instantiation_s));
    inew->var_part = param->item->item; 	/* should be a variable */
    inew->const_part = lookup_instantiation(insts, token->item); 
    if (inst == NULL)
      inst = inext = inew;
    else
      inext = inext->next = inew;
  }
  return inst;
}

int
eval_dynamic(fact_list term, instantiation_list insts, int time) 
{
  int tval = 0;
  char *fname = term->item->item;
  char str[50];
  fact_list fact;
  vertex_t v;

  if (strcmp(fname, "not") == 0) {
    fact = token2fact(dup_token_list(term->item->next));
    tval = !eval_dynamic(fact, insts, time); 
    completely_free_fact_list (fact);
  }
  else
  if (strcmp(fname, "next") == 0) {
    fact = token2fact(dup_token_list(term->item->next));
    tval = eval_dynamic(fact, insts, time + 1); 
    completely_free_fact_list (fact);
  }
  else {
    instantiate_into_string(term->item, insts, str, 0);
    if ((v = lookup_from_table(fact_table[time], str)) && (v->is_true))
      tval = 1;
  }
  if (tval == 0) 
    return 0;
  if (term->next) 
    return eval_dynamic(term->next, insts, time);
  else {
    return 1;
  }
}

#ifdef BBLEARN
int 
eval_rule_body (instantiation_list insts, int time)
{
  if (eval_dynamic(current_control->preconds, insts, time)) {
//    printf("time = %d\n", time);
//    print_instantiation(insts);  
    if (eval_dynamic(current_control->effects, insts, time) == 0) {
//      printf("wrong rule\n");
//      printf("time = %d\n", time);
//      print_instantiation(insts);  
//      print_fact_list(current_control->effects);
      rule_value = 0;
      return 0;
    }
    else {
      current_control->is_used++;
      rule_evaluated = 1;
    }
  }
  return 1;
}

#endif
/* evaulate a formula. now it only supports CNF
 * return: 1: true, 0: faluse
 * future work: and/or relation
 */
int 
eval (fact_list term, instantiation_list insts, int time)
{
  int tval = 0;
  char *fname = term->item->item;
  char str[50], *str1, *str2;
  fact_list fact;
  token_list token, var;
  defpred_list dp;
  static int goal_flag;
  instantiation_list inst_var;
  
#ifdef BBLEARN
  if (term == current_precond) {	/* evalute dynamic rule */
    // printf("OK!\n");
    return eval_rule_body(insts, time);
  }
  else
#endif
  if (strcmp(fname, "forall") == 0) {
    fact = term->next;
    if (lookup_instantiation(insts, fact->item->item)) {
      tval = eval(term->body, insts, time);
    }
    else {
      var = make_generator(fact->item, term->item->next, insts, time);
      inst_var = (instantiation_list)malloc(sizeof(instantiation_s));
      inst_var->var_part = fact->item->item;
      inst_var->next = insts;
      for (; var; var = var->next) {
//	printf("%s\n", var->item);
	inst_var->const_part = var->item;
	tval = eval(term->body, inst_var, time);
      }
      free_token_list(var); 
      inst_var->next = NULL;
      free_instantiation(inst_var); 
    }
    term = term->next;
  }
  else
  if (strcmp(fname, "exists") == 0) {
    fact = term->next;
    if (lookup_instantiation(insts, fact->item->item)) {
      tval = eval(term->body, insts, time);
    }
    else {
      var = make_generator(fact->item, term->item->next, insts, time);
      inst_var = (instantiation_list)malloc(sizeof(instantiation_s));
      inst_var->var_part = fact->item->item;
      inst_var->next = insts;
      for (; var; var = var->next) {
	inst_var->const_part = var->item;
//	printf("%s\n", var->item);
	if ((tval = eval(term->body, inst_var, time)))
	  break;
      }
      free_token_list(var); 
      inst_var->next = NULL;
      free_instantiation(inst_var); 
    }
    term = term->next;
  }
  else
  if (strcmp(fname, "noexists") == 0) {
      fact = term->next;
      var = make_generator(fact->item, term->item->next, insts, time);
      if (var != 0) {
          free_token_list(var); 
          tval = 0;
      }
      else
          tval = eval(term->body, insts, time);
      term = term->next;
  }
  else
  if (strcmp(fname, "not") == 0) {
    fact = token2fact(term->item->next);
    tval = !eval(fact, insts, time); 
    fact->item = 0;
    completely_free_fact_list (fact);
  }
  else
  if (strcmp(fname, "next") == 0) {
    fact = token2fact(term->item->next);
    tval = eval(fact, insts, time + 1); 
    fact->item = 0;
    completely_free_fact_list (fact);
  }
  else
  if (strcmp(fname, "goal") == 0) {
//    fact = token2fact(dup_token_list(term->item->next));
    fact = token2fact(term->item->next);
    goal_flag = 1;
    tval = eval(fact, insts, time); 
    fact->item = 0;
    completely_free_fact_list (fact);
  }
  else
  if (strcmp(fname, "true") == 0) {
    tval = 1;
  }
  else
  if (strcmp(fname, "=") == 0) {
    var = term->item->next;
    str1 = lookup_instantiation(insts, var->item);
    str2 = lookup_instantiation(insts, var->next->item);
    tval = !strcmp(str1, str2);
  }
  else
  if ((dp = lookup_defpred(fname))) {
    inst_var = setup_defpred_instantiation(dp, term->item->next, insts);
    tval = eval(dp->formula, inst_var, time);
    free_instantiation(inst_var); 
  }
  else {
    instantiate_into_string(term->item, insts, str, 0);
    if (goal_flag) {
      goal_flag = 0;
      if (lookup_from_table(goal_table, str)) {
	tval = 1;
      }
    }
    else {
      if (lookup_from_table(fact_table[0], str)) {
	tval = 1;
      }
    }
  }
  if (tval == 0) 
    return 0;
  if (term->next) {
    return eval(term->next, insts, time);
  }
  else {
    return 1;
  }
}

/*
 * check if an instantized action is ruled out by control rules 
 * return: 0: (need to be ruled out) 1: (ok)
 */
int control_check (op_list op, int time)
{
  control_list ctrl;

  for (ctrl = controls; ctrl; ctrl = ctrl->next) {
    if (strcmp(ctrl->name, op->name) == 0) {
      if (eval (ctrl->excludes, op->insts, time)) {
	return 0;
	
      }
    }
  }
  return 1;
}
