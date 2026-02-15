#ifndef __CONTROL_H_
#define __CONTROL_H_

#include "graphplan.h"

typedef struct DEF_PREDICATE {
  char *name;
  param_list params;
  fact_list formula;
  struct DEF_PREDICATE *next;
} defpred_s, *defpred_list, *defpred_ptr;


typedef struct CONTROL_RULE {
  char *name;
  fact_list excludes;
  struct CONTROL_RULE *next;
} control_s, *control_list, *control_ptr;

typedef struct WFF_CONTROL {
  char *name;
  int is_used;
  int condflag;
  fact_list scope, preconds, effects;
  fact_list last_scope, last_precond;
  struct WFF_CONTROL *next;
} wffctrl_s, *wffctrl_list, *wffctrl_prt;


enum { WFF_NORMAL_MODE, WFF_FORCE_MODE };

int eval (fact_list, instantiation_list, int);
token_list make_generator(token_list param, token_list condition, 
			  instantiation_list bind, int);
int control_check (op_list op, int);

#endif
