#ifndef __TIM_H_
#define __TIM_H_

#include "graphplan.h"

#define MAX_NUM_PROPERTY_OBJ_TYPE	10
#define UNIVERSAL_TYPE			~0

enum { UNKNOWN, PROPERTY, ATTRIBUTE };

struct PROPERTY_SPACE;

typedef struct OBJECT_TYPE {
  char *name;
  int type;
  struct OBJECT_TYPE *next;	/* point to the next objects */
} objtype_elt, *objtype_ptr;

typedef struct PREDICATE_TYPE {
  char *name;
  int type;
  struct PREDICATE_TYPE *next;
} predtype_elt, *predtype_ptr;

typedef struct TRANSITION_RULE {
  fact_list enabler;
  fact_list start;
  fact_list finish;
  struct PROPERTY_SPACE *ps;
  struct TRANSITION_RULE *ps_next;
  struct TRANSITION_RULE *next;
} transrule_elt, *transrule_ptr; 

typedef struct PROPERTY_SPACE {
  fact_list property;
  int index;			/* type index */
  int num_obj_types;		/* number of object types */
  int obj_types[MAX_NUM_PROPERTY_OBJ_TYPE];
  int type;			/* attribute or property */
  int num_var;			/* total number of variables in predicate */
  token_list obj;
  fact_list state;		/* use fact_lsit body for states */
  struct TRANSITION_RULE *rule;
  struct PROPERTY_SPACE *root;
  struct PROPERTY_SPACE *next;
} propspace_elt, *propspace_ptr;


int locate_param (char *name, token_list predciate);
void build_transition_rule ();
void inference_type ();
char *find_object_type (char *name, int *type);
int find_predicate_type (char *name);
propspace_ptr find_property_space (token_list token);
propspace_ptr find_property_space (char *name, int i);

#endif
