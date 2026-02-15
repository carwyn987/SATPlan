/****************************************************************/
/* bbio.c							*/
/* revised: Aug., 2000						*/
/* Yi-Cheng Huang 						*/
/****************************************************************/

#include "interface.h"
#include "utilities.h"
#include "control.h"
#include "learn.h"
#include "bbio.h"

enum { NONEED_ATTR = 0, STATIC_ATTR, DYNAMIC_ATTR };
void 
print_literal (literal_ptr lit);


int attr_needed[MAX_NUM_ATTRIBUTE];	
int attr_var_name[MAX_NUM_ATTRIBUTE];
int yyparse();
extern FILE *yyin;
extern op_ptr cur_op;
extern int learn_mode, input_type;
extern char *learnfile;
extern char *domain_name, *control_name;
FILE *learnfp;
FILE *curfp;

#ifdef BBLEARN

extern int num_rule;
extern defpred_list dps;
extern control_list controls;
extern wffctrl_list wffctrls;
extern char* attr_type_name[MAX_NUM_ATTRIBUTE];
extern int orig_num_attr, num_attr;
extern int phase;
extern literal_elt ex_literals[];
extern literal_ptr action_precond_literals, action_effect_literals;
extern literal_elt rule_body[];
extern int num_rule_body_lit;

void
print_ctrl_file_header ()
{
  fprintf(curfp, "(define (control %s)\n"
	  "        (:domain %s)\n\n", control_name, domain_name);
}

void
print_strn (int num, char *str)
{
  for (int i = 0; i < num; i++)
    fprintf(curfp, "%s", str);
}

/* note: it will print indention starting from the next line */
void 
print_indention (int indention)
{
  fprintf(curfp, "\n");
  print_strn(indention, " ");
}

void
print_paren_end ()
{
  fprintf(curfp, ")\n");
}

void
print_indented_paren_end ()
{
  fprintf(curfp, "  )\n\n");
}

int 
same_fact_list (fact_list f1, fact_list f2)
{
  char *s;
  while (f1 && f2) {
    if (equal_facts(f1->item, f2->item) == 0)
      return 0;
    s = f1->item->item;
    if (strcmp(s, "exists") == 0 || strcmp(s, "forall") == 0) {
      f1 = f1->body;
      f2 = f2->body;
    }
    else {
      f1 = f1->next;
      f2 = f2->next;
    }
  }
  if (f1 != 0 || f2 != 0)
    return 0;
  return 1;
}

int
redundant_graph_control (control_list rule)
{
  for (control_list r = controls; r != rule; r = r->next) {
    if (same_fact_list(r->excludes, rule->excludes)) {
      return 1;
    }
  }
  return 0;
}

int
redundant_wff_control (wffctrl_list rule)
{
  for (wffctrl_list r = wffctrls; r != rule; r = r->next) {
    if (same_fact_list(r->scope, rule->scope) &&
	same_fact_list(r->preconds, rule->preconds) &&
	same_fact_list(r->effects, rule->effects))
      return 1;
  }
  return 0;
}


/************************************************************************/
/* routines for printing verified rules					*/
/************************************************************************/

void
print_typed_variable (token_list var, int flag)
{
  if (flag)
    fprintf(curfp, " ");
  fprintf(curfp, "%s", var->item);
  if (var->next)
    fprintf(curfp, "- %s", var->next->item);
}

void 
print_predicate (token_list predicate) 
{
  char *pred_name = predicate->item;

  if (strcmp(pred_name, "goal") == 0 || strcmp(pred_name, "not") == 0 ||
      strcmp(pred_name, "next") == 0) {
    fprintf(curfp, "(%s ", pred_name);
    print_predicate(predicate->next);
    fprintf(curfp, ")");
  }
  else
    print_token_list(curfp, predicate);
  
}

void
print_rule_facts (fact_list facts)
{
  int flag, num_paren = 0;
  int indention = 4; 
  char *pred_name;
  
  flag = 0;
  while(facts) {
    pred_name = facts->item->item;
    if (strcmp(pred_name, "exists") == 0 || strcmp(pred_name, "forall") == 0) {
      num_paren++;
      print_indention(indention);
      fprintf(curfp, "(%s (", pred_name);
      print_typed_variable(facts->next->item, 0);
      fprintf(curfp, ") ");
      print_predicate(facts->item->next);
      indention += 2;
      facts = facts->body;
    }
    else {
      print_indention(indention);
      if ((facts->next) && (flag == 0)) {
	flag = 1;
	num_paren++;
	fprintf(curfp, "(and ");
	indention += 5;
      }
      print_predicate(facts->item);
      facts = facts->next;
    }
  }
  print_strn(num_paren, ")");
  fputc('\n', curfp);
}

void
print_defpredicate ()
{
  int flag;
  defpred_list dp;
  param_list param;

  for (dp = dps; dp; dp = dp->next) {
    fprintf(curfp, "  (:defpredicate %s\n   :parameters (", dp->name);
    flag = 0;
    for (param = dp->params; param; param = param->next) {
      print_typed_variable(param->item, flag);
      flag = 1;
    }
    fprintf(curfp, ")\n   :body ");
    print_rule_facts(dp->formula);
    print_indented_paren_end();
  }
}

void
print_graph_control ()
{
  control_list control;
  for (control = controls; control; control = control->next) {
    if (redundant_graph_control(control))
      continue;
    num_rule++;
    fprintf(curfp, "  (:action %s\n   :exclude", control->name);
    print_rule_facts(control->excludes);
    print_indented_paren_end();
  }
}

void 
print_wff_control ()
{
  wffctrl_list wffctrl;
  
  for (wffctrl = wffctrls; wffctrl; wffctrl = wffctrl->next) {
    if (redundant_wff_control(wffctrl))
      continue;
    num_rule++;
    fprintf(curfp, "  (:wffctrl %s\n   :scope", wffctrl->name);
    print_rule_facts(wffctrl->scope);
    fprintf(curfp, "   :precondition");
    print_rule_facts(wffctrl->preconds);
    fprintf(curfp, "   :effect");
    print_rule_facts(wffctrl->effects); 
    print_indented_paren_end();
  }
}		   

void
print_verified_rules ()
{
  //if (controls || wffctrls) 
  //  fprintf(curfp, ";;; the following are verified rules\n\n");
  print_defpredicate();
  print_graph_control();
  print_wff_control();
}


/************************************************************************/
/* routines for printing learned rules					*/
/************************************************************************/

void
print_and (int indention)
{
  print_indention(indention);
  fprintf(curfp, "(and ");
}

void 
print_true ()
{
  fprintf(curfp, "(true)");  
}

void
make_attr_var_name (int attr, char* name)
{
  int i;
  fact_list params;
  if (attr < orig_num_attr) {
    for (i = 0, params = cur_op->params; params; 
	 params = params->next, i++) {
      if (i == attr) {
	sprintf(name, "%s", params->item->item);
	break;
      }
    } 
  }
  else
    sprintf(name, "?bbv%c", attr_var_name[attr] + 'a');
}

void 
print_rule_literal (literal_ptr lp)
{
  int i, var, num_paren = 1, lit_type = lp->lit_type;
  char vname[50], *lit_name;
  
  lit_name = lp->lit_name;
  if (lit_type == PRED_LIT) {
    if (strncmp(lit_name, "bbun", 4) == 0) {
      lit_name = &(lit_name[4]);
      fprintf(curfp, "(not ");
      num_paren++;
    }
  } 
  if (lit_type == NOT_PRED_LIT) {
    if (strncmp(lit_name, "bbun", 4) == 0)
      lit_name = &(lit_name[4]);
    else {
      fprintf(curfp, "(not ");
      num_paren++;
    }
  } 
  if (lit_type == UNEQUAL_LIT) {
    fprintf(curfp, "(not ");
    num_paren++;
  }
  if (lp->bk_type == GOAL) {
    fprintf(curfp, "(goal ");
    num_paren++;
  }
  switch(lit_type) {
  case PRED_LIT:
  case NOT_PRED_LIT:	
    fprintf(curfp, "(%s", lit_name);
    break;
  case EQUAL_LIT:
  case UNEQUAL_LIT:
    fprintf(curfp, "(=");
    break;
  }
  for (i = 1; i <= lp->num_var; i++) { 
    var = lp->binding[i];
    make_attr_var_name(var, vname);
    fprintf(curfp, " %s", vname);
  }
  print_strn(num_paren, ")");
}

int
find_last_binding (literal_ptr lp)
{
  int last = -1;
  for (int i = 1; i <= lp->num_var; i++)
    if (lp->binding[i] > last)
      last = lp->binding[i];
  return last;
}

void 
print_rule_var (int indention, int attr)
{
  char vname[50];
  literal_ptr lp;
  print_indention(indention);
  if (attr_needed[attr] == STATIC_ATTR)
    fprintf(curfp, "(exists ");
  else
    fprintf(curfp, "(forall ");
  make_attr_var_name(attr, vname);
  fprintf(curfp, "(%s) ", vname);
  lp = &(ex_literals[attr]);
  if ((attr >= orig_num_attr) && (find_last_binding(lp) == attr) &&
      (attr_needed[attr] == STATIC)) {
    print_rule_literal(lp);
  }
  else {
    if (attr_type_name[attr])
      fprintf(curfp, "(%s %s)", attr_type_name[attr], vname);
    else
      fprintf(curfp, "(true)");
  }
}

char*
find_action_param_name (int loc)
{
  int i;
  fact_list param;
  for (i = 0, param = cur_op->params; param; param = param->next, i++) {
    if (loc == i)
      return param->item->item;
  }
}


void 
update_needed_attr (int attr)
{
  int *binding, i, bk_type;
//  int bk_type = attr_lp->bk_type;
  literal_ptr lp;

  if (attr == FREE_BINDING)
    return;
  if (attr_needed[attr] == DYNAMIC_ATTR)
    return;
  lp = &(ex_literals[attr]);
  bk_type = lp->bk_type;
  
  for (i = 1; i <= ex_literals[attr].num_var; i++)
      if (ex_literals[attr].binding[i] == i)
          break;

  if (attr >= orig_num_attr) {
//   if (lp->bind_type[i] == FREE_BINDING) {
      if (attr_needed[attr] == NONEED_ATTR) 
	attr_needed[attr] = (bk_type == DYNAMIC) ? DYNAMIC_ATTR : STATIC_ATTR; //     return;
//   }
//   else {
//     printf("tst\n");
     
        
//    }    
    /* if bind_type is not set properly, it may cause infinite 
       recursive calls; some handling rounted need here */ 
  }
  else {
    attr_needed[attr] = STATIC_ATTR;
    return;
  }
  /*
  if (attr_needed[attr] == STATIC_ATTR) {
    if (attr_lp->bk_type == DYNAMIC)
      attr_needed[attr] = DYNAMIC_ATTR;
    return;
  } 
  attr_needed[attr] = 
    ((attr >= orig_num_attr) && (attr_lp->bk_type == DYNAMIC)) 
    ? DYNAMIC_ATTR : STATIC_ATTR; */
  binding = lp->binding;
  for (int i = 1; i <= lp->num_var; i++) {
      if (binding[i] == attr)
          continue;
      update_needed_attr(binding[i]);
//    update_needed_attr(binding[i], i, lp);
  }
}

literal_ptr
get_first_effect_literal (int rule_type)
{
  literal_ptr lp;
  for (lp = action_effect_literals; lp; lp = lp->next) {
    if (rule_type == -1) {
      if (lp->lit_type == NOT_PRED_LIT)
	return lp;
    }
    else
      if (lp->lit_type == PRED_LIT)
	return lp;
  }
  return action_effect_literals;  /* else return the first */
}

void 
print_scope (int rule_type)
{
  int i, start_attr, num_paren, indention, *binding, first_flag, var_count;
  literal_ptr lp;
  
  num_paren = var_count = 0; 
  indention = 4;
//  fprintf(curfp, ";\n");
  if (phase == STATIC && rule_type == -1) {
    start_attr = orig_num_attr;
    fprintf(curfp, "  (:action %s\n   :exclude", cur_op->name);
  }
  else {
    start_attr = 0;
    fprintf(curfp, "  (:wffctrl %s\n   :scope", cur_op->name);
  }
  /* print dynamic variables first - forall */
  for (i = start_attr; i < num_attr; i++) {
    if (attr_needed[i] == DYNAMIC_ATTR) {
      num_paren++;
      if ((i >= orig_num_attr))
	attr_var_name[i] = var_count++;
      print_rule_var(indention, i);
      indention += 2;
    }    
  }
  /* print static variables - exists */
  for (i = start_attr; i < num_attr; i++) {
    if (attr_needed[i] == STATIC_ATTR) {
      num_paren++;
      if ((i >= orig_num_attr)) {
	attr_var_name[i] = var_count++;
      }
      print_rule_var(indention, i);
      indention += 2;
    }    
  }
  num_paren++;
  indention += 2;
  print_and(indention);
  indention += 5;
  first_flag = 1;
  /*
  for (i = orig_num_attr; i < num_attr; i++) {
  lp = &(ex_literals[i]);
    if (attr_needed[i] != NONEED_ATTR) {
      if ((find_last_binding(i) == i) && (lp->bk_type != DYNAMIC)) {
	if (first_flag)
	  first_flag = 0;
	else
	  print_indention(indention);
	print_rule_literal(lp);
      }
    }    
  } */
  if (num_rule_body_lit == 0)
    print_true();
  else 
    for (i = 0; i < num_rule_body_lit; i++) {
      lp = &(rule_body[i]);
      if (lp->bk_type == DYNAMIC)
	continue;
      if (first_flag)
	first_flag = 0;
      else
	print_indention(indention);
      print_rule_literal(lp);
    }
  print_strn(num_paren, ")");
  fprintf(curfp, "\n");
}

void 
print_rule_precond ()
{
  int i, indention, first_flag, flag = 0;
  literal_ptr lp;

  fprintf(curfp, "   :precondition");
  indention = 4;
  print_and(indention);
  indention += 5;
  first_flag = 1;
  for (i = orig_num_attr; i < num_attr; i++) {
    if (attr_needed[i] != NONEED_ATTR) {
      lp = &(ex_literals[i]);
      if ((find_last_binding(lp) == i) && (lp->bk_type == DYNAMIC)) {
	if (first_flag)
	  first_flag = 0;
	else
	  print_indention(indention);
	print_rule_literal(lp);
	flag = 1;
      }
    }    
  }
  for (i = 0; i < num_rule_body_lit; i++) {
    lp = &(rule_body[i]);
    if (lp->bk_type != DYNAMIC)
      continue;
    if (first_flag)
      first_flag = 0;
    else
      print_indention(indention);
    print_rule_literal(lp);
    flag = 1;
  }
  for (lp = action_precond_literals; lp; lp = lp->next) {
    if (lp->bk_type == STATIC)
      continue;
    if (first_flag)
      first_flag = 0;
    else
      print_indention(indention);
    print_rule_literal(lp);
    flag = 1;
  }
  if (flag == 0)
    print_true();
  fprintf(curfp, ")\n");
}

void 
print_rule_effect (int rule_type)
{
  literal_ptr lp;
  fprintf(curfp, "   :effect (next ");
  lp = get_first_effect_literal(rule_type);
  if (rule_type == -1)
    lp->lit_type = (lp->lit_type == NOT_PRED_LIT) ? PRED_LIT : NOT_PRED_LIT;
  print_rule_literal(lp);
  if (rule_type == -1)
    lp->lit_type = (lp->lit_type == NOT_PRED_LIT) ? PRED_LIT : NOT_PRED_LIT;
  print_paren_end();
}

/* print a control rule to the control rule file	*/
void
print_rule (int rule_type)
{
  int i, *binding, j, k;
  literal_ptr lp;

  for (i = 0; i < num_attr; i++)
    attr_needed[i] = NONEED_ATTR;

  if (num_rule_body_lit == 0) {
    for (i = orig_num_attr; i < num_attr; i++)
      if (ex_literals[i].bk_type == GOAL) {
          update_needed_attr(i);
      }
  }
  else {
    for (k = 0; k < num_rule_body_lit; k++) {
      lp = &(rule_body[k]);
      binding = lp->binding;
      for (i = 1; i <= lp->num_var; i++) {
          update_needed_attr(binding[i]);
      }
    }
  }
  
  for (lp = action_effect_literals; lp; lp = lp->next) {
    for (i = 1; i <= lp->num_var; i++)
      attr_needed[lp->binding[i]] = DYNAMIC_ATTR;
  }
  lp = get_first_effect_literal(rule_type);
  for (i = 1; i <= lp->num_var; i++)
    attr_needed[lp->binding[i]] = DYNAMIC_ATTR;
  j = k = 0;
  for (i = 0; i < num_attr; i++) {
    if (attr_needed[i] == DYNAMIC_ATTR)
      j++;
    else
      if (attr_needed[i] != NONEED_ATTR)
	k++;
  }
 
/* 
  for (i = 0; i < num_attr; i++)
      printf ("%d ", attr_needed[i]);
  printf("\n");
  */

  if (j > 5 || j+k > 8)
    return;
  switch(rule_type) {
  case 1:
    if (num_rule_body_lit)
      fprintf(curfp, "; select rules\n");
    else
      fprintf(curfp, "; immediately select rules\n");
    break;
  case -1:
    fprintf(curfp, "; reject rules\n");
  }
  print_scope(rule_type);
  if (phase == DYNAMIC || rule_type == 1) {
    print_rule_precond();
    print_rule_effect(rule_type);
  }
  print_indented_paren_end();
}

/* load a control rule from the temporary file: ".bb.tmp" 	*/
void 
load_rule (int rule_type)
{
  /*
  if ((curfp = fopen("bb.tmp", "a")) != NULL) {
    print_rule(rule_type);
    fclose(curfp);
  } */
  if ((curfp = fopen(".bb.tmp", "w")) != NULL) {
    print_ctrl_file_header();
    print_rule(rule_type);
    print_paren_end();
    fclose(curfp);
    if ((yyin = fopen(".bb.tmp", "r")) != NULL) {
      yyparse();
    }
    fclose(yyin);
  }
  curfp = learnfp;
}
#endif

/* open control rule files	*/
void
open_control_file ()
{
  int i;
  char str[100];

  if ((yyin = fopen(learnfile,"r")) != NULL) {
#ifdef BBLEARN
    learn_mode |= VERIFY_CONTROL;
#endif
    input_type = CONTROL_INPUT;
    fprintf(STDMSG, "Loading control file for verifying: %s\n", learnfile);
    yyparse();
    fclose(yyin);
  }
  i = strlen(learnfile);
  strcpy(str, learnfile);
  strcat(str, ".bak");
  rename(learnfile, str);
  if (control_name == 0)
    control_name = "learned_control";
  if ((learnfp = fopen(learnfile, "w")) == NULL)
    do_error("cannot open learning output file."); 
  curfp = learnfp;
}




