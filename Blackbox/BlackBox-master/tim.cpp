#include <stdlib.h>
#include "utilities.h"
#include "interface.h"
#include "tim.h"
#include "learn.h"

#ifdef BBLEARN

//#define BBDEBUG

extern op_list ops;
extern fact_list the_types;
extern fact_list initial_facts;
extern fact_list predicates, constants;
extern token_list negation_predicates, objects;
extern char *bbun_str;

objtype_ptr objtypes = 0;
predtype_ptr predtypes = 0;
propspace_ptr propspaces = 0;
transrule_ptr transrules = 0;

#ifdef BBDEBUG
void 
print_transition_rule (transrule_ptr rule)
{
  printf("enabler: ");
  print_fact_list (rule->enabler);
  printf("start(delete): ");
  print_fact_list (rule->start);
  printf("finished(add): ");
  print_fact_list(rule->finish);
}


void
print_property_space ()
{
  for (propspace_ptr p = propspaces; p; p = p->next) {
    if (p->root == p) {
      print_fact_list (p->property);
      if (p->type == PROPERTY)
	printf ("PROPERTY\n");
      else
	if (p->type == ATTRIBUTE)
	  printf ("ATTRIBUTE\n");
	else
	  if (p->type == UNKNOWN)
	    printf ("UNKNOWN\n");
      printf ("state: ");
      for (fact_list f = p->state; f; f = f->next)
	print_fact_list(f->body);
      printf ("\nobject: ");
      print_token_list (STDMSG, p->obj);
      printf ("\nobj_types %d:", p->num_obj_types);
      for (int i = 0; i < p->num_obj_types; i++)
	printf ("[%d]", p->obj_types[i]);
      printf ("\n");
      for (transrule_ptr r = p->rule; r; r = r->ps_next) {
	print_transition_rule(r);
	printf ("---------------\n");
      }
      printf ("\n===================\n");
    }
  } 
}

void 
print_predicate_types ()
{
  predtype_ptr p;

  for (p = predtypes; p; p = p->next) 
    printf("%s %d\n", p->name, p->type);
}

#endif

/* compare two fact lists */
/* return 0: if two facts are equal; 1:otherwise */
int 
fact_comp (fact_list f1, fact_list f2)
{
  if (f1 && f2)		/* both are non-null */
    return !equal_facts(f1->item, f2->item);
  if (f1 || f2)		/* one null; one non-null */
    return 1;
  return 0;		/* both are null */
}

/* compare two transition rules       */
/* return 0: if r1 = r2; 1: otherwise */
int 
transrule_comp(transrule_ptr r1, transrule_ptr r2)
{
  if (fact_comp(r1->enabler, r2->enabler))
    return 1;
  if (fact_comp(r1->start, r2->start))
    return 1;
  return fact_comp(r1->finish, r2->finish);
}

/* add a transition rule into rule sets */
void 
add_transition_rule (transrule_ptr rule)
{
  transrule_ptr prev, cur;
  for (prev = cur = transrules; cur; prev = cur, cur = cur->next)
    if (transrule_comp(cur, rule) == 0)	/* same rule in the rule set */
      return;
  if (transrules == 0)
    transrules = rule;
  else 
    prev->next = rule;
}

/* return the location of the parameter in the predicate */
/* return 0: didn't find, otherwise: the location        */
int 
locate_param (char *name, token_list predicate)
{
  int loc;
  token_list t;
  /* skip the name for the predicate */
  for (loc = 1, t = predicate->next; t; t = t->next, loc++)
    if (strcmp(t->item, name) == 0)
      return loc;
  return 0;
}

/* extract property from precondition, or effects           */
/* type: 0: delete effects; 1: add effects or preconditions */
fact_list 
extract_property(token_list param, fact_list facts, int type)
{
  int loc;
  char str[100];
  token_list token, ttemp;
  fact_list property = NULL, new_property;
  char *param_name = param->item;
 
  for (fact_list f = facts; f; f = f->next) {
    token = f->item;
    if (type == 0) {				/* delete effects */
      if (strcmp(token->item, DELETE) == 0) 
	token = token->next; 
      else
	continue;
    }	
    else {					/* add effect */
      if (strcmp(token->item, DELETE) == 0)
	continue;
    }
    if ((loc = locate_param (param_name, token)) > 0) {
      ttemp = strdup2token(token->item);
      sprintf(str, "%d", loc);       ttemp->next = strdup2token(str); 
      new_property = token2fact(ttemp);
      property = fact_list_append(property, new_property);
    }
  }	
  return property;
}

/* simply form a transition rule */
transrule_ptr
make_transition_rule (fact_list enabler, fact_list start, fact_list finish)
{
  transrule_ptr rule = (transrule_ptr)calloc(1, sizeof(transrule_elt));
  rule->enabler = enabler;
  rule->start = start;
  rule->finish = finish;
  return rule;
}

/* build one transition rule for one parameter in the action "op" */
transrule_ptr
build_one_transition_rule (token_list param, op_list op)
{
  fact_list fact, prev_fact, ftemp;
  transrule_ptr rule;

  rule = make_transition_rule (extract_property(param, op->preconds, 1),
			       extract_property(param, op->effects, 0),
			       extract_property(param, op->effects, 1));

  /* purge delete effects on enabler: enabler = preconds - del effects */
  for (prev_fact = fact = rule->enabler; fact;) {
    if (find_fact_list(rule->start, fact->item)) {
      ftemp = fact;
      if (fact == rule->enabler)
        rule->enabler = fact->next;
      else
	prev_fact->next = fact->next;
      fact = fact->next;
      ftemp->next = NULL;
      free_fact_list(ftemp);
    }
    else {
      prev_fact = fact;
      fact = fact->next;
    }
  }
  return rule;
}

/* split a transition rule if necessary */
/* return: a set of splitted rules */
void
split_rule (transrule_ptr r)
{
  int flag;
  transrule_ptr new_rule, cur = r;
  fact_list s, f, ps, pf, temp;

  for (ps = s = r->start; s;) {
    flag = 0;
    for (pf = f = r->finish; f; pf = f, f = f->next) {
      if (equal_facts(s->item, f->item)) {
	new_rule = (r->enabler) ?
	  make_transition_rule(token2fact(dup_token_list(r->enabler->item)), 
			       s, f)
	  : make_transition_rule(0, s, f);
	cur = cur->next = new_rule;
	temp = s;
	if (s == r->start)	/* remove token in the original rule */
	  r->start = s->next;	/* it will be used in the new rule */
	else 
	  ps->next = s->next;
	s = s->next;
	if (f == r->finish)
	  r->finish = f->next;
	else
	  pf->next = f->next;
	temp->next = f->next = 0;
	flag = 1;
	break;
      }
    }
    if (flag == 0) {
      s = s->next;
      ps = s;
    }
  }
}

/* build transition rules from operators */
void 
build_transition_rule ()
{
  op_list op;
  fact_list fact;
  transrule_ptr rule, nr, r;

  for (op = ops; op; op = op->next) {
    for (fact = op->params; fact; fact = fact->next) {
      rule = build_one_transition_rule(fact->item, op);
      split_rule(rule);
      for (r = rule; r; r = nr) {
	nr = r->next;
	/* skip null transition rules */
	if (r->start == 0 && r->finish == 0) {	
	  if (r->enabler != 0)
	    free_fact_list(r->enabler);
	  free(r);
	  continue;
	}
	else {
	  // print_transition_rule(r);
          // printf ("==============\n");
	  add_transition_rule(r);
	}
      }
    }
  }
  /*
  for (transrule_ptr r = transrules; r; r = r->next) {
    print_transition_rule(r);
    printf ("---------------\n");
    } 
  */ 
}

/* make a property */
fact_list 
make_property (char *name, int loc)
{
  char str[100];
  token_list token;
  
  token = strdup2token(name);
  sprintf(str, "%d", loc);
  token->next = strdup2token(str);
  return token2fact(token);
}

/* create initial property space (equivalence class) for a predicate */
void
add_property_space (char *name, int num_var)
{
  int s;
  propspace_ptr p;

  s = (num_var > 0) ? 1 : 0;
  for (int i = s; i <= num_var; i++) {
    p = (propspace_ptr)calloc(1, sizeof(propspace_elt));
    p->property = make_property(name, i); 
    p->root = p;
    p->type = UNKNOWN;
    p->num_var = num_var;
    if (propspaces)	/* now add into property space list */
      p->next = propspaces;
    propspaces = p;
  }
}

/* initialize and property space equivalence classes */
void
init_property_space (void)
{
  int num_var;
  char *name, str[100];

  for (fact_list f = predicates; f; f = f->next) {
    name = f->item->item;
    num_var = get_predicate_variable_number(name);
    add_property_space(name, num_var);
    if (lookup_negation_predicate (name)) {
      sprintf(str, bbun_str, name);
      add_property_space(str, num_var);
    }
  }
}

/* find a property_space */
propspace_ptr
find_property_space (token_list token)
{
  for (propspace_ptr p = propspaces; p; p = p->next) {
    if (equal_facts(p->property->item, token))
      return p;
  }
  return 0;
}

propspace_ptr
find_property_space (char *name, int i)
{
  char str[10];
  token_list p;
  propspace_ptr ps;

  p = strdup2token(name);
  sprintf(str, "%d", i);
  p->next = strdup2token(str);
  ps = find_property_space(p);
  free_token_list(p);
  return ps;
}

propspace_ptr
find_property_root (propspace_ptr p)
{
  for (; p != p->root; p = p->root) ;
  return p;
}

void 
union_property_list (propspace_ptr seed, fact_list f)
{
  propspace_ptr p;
  for (; f; f = f->next) {
    p = find_property_space(f->item);
    if (find_property_root(seed) != find_property_root(p))
      p->root = seed;
  }
}

/* seed the property spaces and distinguish property and attribute space */
void
seed_property_spaces ()
{
  propspace_ptr seed, p, ptemp;
  fact_list f, pf;
  
  init_property_space();
  for (transrule_ptr r = transrules; r; r = r->next) {
    if (r->start)
      seed = find_property_space(r->start->item);
    else
      seed = find_property_space(r->finish->item);
    union_property_list(seed, r->start);
    union_property_list(seed, r->finish);
  }
  /* now assign unique type index to each property space */
  int index = 1;
  for (p = propspaces; p; p = p->next) {
    if (p->root == p) {		/* root of a property space */
      p->index = index;
      index = index << 1;
    }
    else {
      /* path compression */
      ptemp = find_property_root(p);
      p->root = ptemp;
      p->index = ptemp->index;
    }
  } 
  for (p = propspaces; p; p = p->next) {
    /* path compression */
    ptemp = find_property_root(p);
    if (ptemp != p) {
      p->root = ptemp;
      p->index = ptemp->index;
      /* now add property into the root of property space */
      for (pf = f = ptemp->property; f; pf = f, f = f->next) ;
      pf->next = p->property; 
    }
  }
}

/* assign transition rules into property spaces */
void 
assign_transition_rule ()
{
  int type;
  token_list token;
  propspace_ptr p;
  for (transrule_ptr r = transrules; r; r = r->next) {
    if (r->start) {
      token = r->start->item;
      type = (r->finish) ? PROPERTY : ATTRIBUTE;
    }
    else {
      token = r->finish->item;
      type = ATTRIBUTE;
    }
    p = find_property_space(token);
    p = p->root;    	/* should be root after path compresstion */
    if (p->type != ATTRIBUTE)
      p->type = type;
    if (p->rule)
      r->ps_next = p->rule;
    p->rule = r;
    r->ps = p;
  }

  for (p = propspaces; p; p = p->next)
    if ((p->root == p) && (p->type == UNKNOWN))
      p->type = ATTRIBUTE;
  /*
  print_property_space ();
  for (transrule_ptr r = transrules; r; r = r->next) {
    print_fact_list(r->ps->property);
    printf (" %d\n", r->ps->type);
  }
  printf ("============\n");
  for (p = propspaces; p; p = p->next) {
    print_fact_list(p->property);
    printf (" %d %d \n", p->root->type, p->root->index);
    for (transrule_ptr r = p->rule; r; r = r->ps_next)
      print_transition_rule(r);
    printf("------------\n");
    }
  */
}

void 
add_object2property_space (propspace_ptr p, char *name)
{
  token_list obj, prev_obj;
  
  for (prev_obj = obj = p->obj; obj; prev_obj = obj, obj = obj->next) {
    if (strcmp(obj->item, name) == 0)
      return;
  }
  obj = strdup2token(name);
  if (p->obj == 0)
    p->obj = obj;
  else {
    prev_obj->next = obj;
  }
}

/* find initail property for an object */
fact_list 
find_initial_property (char *obj_name)
{
  int flag, loc;
  fact_list f;
  token_list tobj, ttemp;
  fact_list property = 0, pnew, ptemp, pp;

  for (f = initial_facts; f; f = f->next) {
    tobj = f->item;
    for (loc = 1, ttemp = tobj->next; ttemp; ttemp = ttemp->next, loc++) {
      if (strcmp(ttemp->item, obj_name) == 0) {
	flag = 0;
	pnew = make_property (tobj->item, loc);
	for (pp = ptemp = property; ptemp; pp = ptemp, ptemp = ptemp->next) {
	  /* make sure no duplication */
	  if (equal_facts(ptemp->item, pnew->item)) {
	    flag = 1;
	    free_fact_list(pnew);
	    break;
	  }
	}
	if (flag == 0) {	
	  if (property == 0)
	    property = pnew;
	  else
	    pp->next = pnew;
	}
      }
    }
  }
  return property;
}

int 
count_state (fact_list s)
{
  int i = 0;
  for (; s; s = s->next)
    i++;
  return i;
}


/* compare two states: a state is a bag of properties 	*/
/* return 1: if two state are equal;   		      	*/
/*        2: if state2 is a superset of state1 	      	*/
/*        0: states are not equal              		*/
int
equal_state (fact_list state1, fact_list state2)
{
  fact_list s1, s2;
  for (s1 = state1; s1; s1 = s1->next) {
    for (s2 = state2; s2; s2 = s2->next) {
      if (equal_facts(s1->item, s2->item))
	break;
    }
    if (s2 == 0)
      return 0;
  }
  /* this superset comparison is for extending property spaces */
  if (count_state(state1) < count_state(state2))
    return 2;
  return 1;
}

/* add a bag of state into a property space */
void
add_state2property_space (propspace_ptr ps, fact_list state)
{
  fact_list slist, snew;

  for (slist = ps->state; slist; slist = slist->next) {
    if (equal_state(slist->body, state) == 1) {
      return;
    }
  }
  /* !!! */
  /* need an extra fact_list node as the state head */
  /* take care of this if the memory will be freed later */
  snew = (fact_list)calloc(1, sizeof(fact_list_elt));
  snew->body = dup_fact_list(state);
  
  if (ps->state != 0)
    snew->next = ps->state;
  ps->state = snew;
}

/* assign state to a property space from the initial property of an object */
void
assign_property_space_state (propspace_ptr ps, char *oname, fact_list objprop)
{
  int flag = 0;
  fact_list psp, prop = 0, pnew, objp;

  if (ps->root != ps)		/* not the root of property space */
    return;
  for (psp = ps->property; psp; psp = psp->next) {
    for (objp = objprop; objp; objp = objp->next) {
      if (equal_facts(psp->item, objp->item)) {
	flag = 1;
	pnew = token2fact(dup_token_list(psp->item));
	if (prop != 0)
	  pnew = prop->next;
	prop = pnew;
      }
    }
  }
  if (flag) {
    add_object2property_space(ps, oname); 
    if (ps->type != ATTRIBUTE) {
      add_state2property_space(ps, prop);
    }
    free_fact_list (prop);
  } 
}

/* assign initail states for property space */
void
assign_initial_state (void)
{
  char str[100];
  token_list token;
  token_list_elt property, propnext;
  fact_list objprop;
  objtype_ptr o;
  propspace_ptr ps;

  propnext.next = 0;
  propnext.item = str;
  property.next = &propnext; 
  for (token = objects; token; token = token->next) {
    o = (objtype_ptr)calloc(1, sizeof(objtype_elt));
    o->name = strdup(token->item);	
    if (objtypes)
      o->next = objtypes;
    objtypes = o;
    objprop = find_initial_property(token->item);
//    printf("%s\n", token->item);
//    print_fact_list (objprop);
//    printf("here\n");
    for (ps = propspaces; ps; ps = ps->next) 
      assign_property_space_state (ps, o->name, objprop);
    // printf ("%s\n", o->name);
    
    // print_fact_list (objprop);
    // add_object_property_space(p, o->name);
  }
  // print_property_space_state();
}

/* find property in a state                  */
/* return 1: if property in the state        */
/*        0: if property is not in the state */
int
find_property_in_state (fact_list state, fact_list property)
{
  fact_list s, p;

  for (p = property; p; p = p->next) {
    for (s = state; s; s = s->next) {
      if (equal_facts(p->item, s->item))
	break;
    }
    if (s == 0)
      return 0;
  }
  return 1;
}

/* update the state by a transition rule                               */
/* return: state (it is the caller's responsibility to free the state) */
fact_list 
update_state_by_rule (fact_list state, transrule_ptr rule)
{
  fact_list news, s, prev, rs, tmp;
  
  news = dup_fact_list(state);
  for (rs = rule->start; rs; rs = rs->next) { 	/* remove start */
    for (prev = s = news; s;) {
      if (equal_facts(rs->item, s->item)) {
	tmp = s;
	if (s == news)
	  news = s->next;
	prev = s->next;
	s = s->next;
	tmp->next = NULL;
	free_fact_list(tmp);
      }
      else {
	prev = s;
	s = s->next;
      }
    }
  }
  for (rs = rule->finish; rs; rs = rs->next) { 	/* add finish */
    for (s = prev = news; s; s = s->next) {
      if (equal_facts(rs->item, s->item))
	break;
    }
    if (s == 0) {
      tmp = token2fact(dup_token_list(rs->item));
      if (news == 0)
	news = tmp;
      else
	prev->next = tmp;
    }

  }
  return news;
}

/* extend a state by transition rules                 */
/* return 0: if property space become attribute space */
/*        1: normal                                   */
int
extend_state_by_rule (fact_list state, propspace_ptr ps)
{
  int i;
  fact_list ns, newgen = NULL, tmp, s, prevs;
  transrule_ptr r;
  
  /* rule use property state next pointer: ps_next */
  for (r = ps->rule; r; r = r->ps_next) { 
    if (find_property_in_state(state, r->start)) {
      ns = update_state_by_rule(state, r);
      tmp = (fact_list)calloc(1, sizeof(fact_list_elt));
      tmp->body = ns;
      for (prevs = s = newgen; s; prevs = s, s = s->next) {
	if ((i = equal_state(s->body, ns))) {
	  if (i == 2) {
	    free_fact_list(tmp);
	    free_fact_list(newgen);
	    return 0;
	  }
	  free_fact_list(tmp);
	  break;
	}
      }
      if (s == 0) {
	if (newgen == 0)
	  newgen = tmp;
	else
	  prevs->next = tmp;
      } 
    }  
  }
  /* add newgen into property space */
  for (s = newgen; s; s = s->next) {
    // print_fact_list (s->body);
    add_state2property_space(ps, s->body); 
  }
  free_fact_list(newgen);
  return 1;
}

/* extend the "property" spaces */
void
extend_property_spaces (void)
{
  fact_list state;
  propspace_ptr ps;
  
  for (ps = propspaces; ps; ps = ps->next) {
    if (ps != ps->root || ps->type != PROPERTY)
      continue;
    //print_fact_list (ps->property);
    for (state = ps->state; state; state = state->next) 
      if (extend_state_by_rule(state->body, ps) == 0) {
	ps->type = ATTRIBUTE;
	break;
      }
    // printf ("-----------\n");
  }
}

/* extend a single attribute space */
void
extend_one_attribute_space (propspace_ptr pspace)
{
  token_list obj;
  propspace_ptr ps;
  transrule_ptr r;
  fact_list prop, ptmp;

  if (pspace->type != ATTRIBUTE)
    return;
  pspace->type = -(pspace->type);   /* mark as exteneded */
  for (r = pspace->rule; r; r = r->ps_next) {
    for (ps = propspaces; ps; ps = ps->next) {
      if (ps == ps->root && ps->type == ATTRIBUTE && ps != pspace) {
	for (prop = r->enabler; prop; prop = prop->next) {
	  ptmp = token2fact(dup_token_list(prop->item));
	  if (find_property_in_state(ps->property, ptmp))
	    extend_one_attribute_space(ps);
	  free_fact_list(ptmp);
	}
      }
    }
  }
  for (r = pspace->rule; r; r = r->ps_next) {
    if (r->start == NULL && r->finish)
      for (ps = propspaces; ps; ps = ps->next) {
	for (prop = r->enabler; prop; prop = prop->next) {
	  ptmp = token2fact(dup_token_list(prop->item));
	  if (find_property_in_state(ps->property, ptmp)) {
	    for (obj = ps->obj; obj; obj = obj->next)
	      add_object2property_space(pspace, obj->item);
	  }
	  free_fact_list(ptmp);	  
	}
      }
  }
}

/* extend attributes spaces */
void 
extend_attribute_spaces (void)
{
  propspace_ptr ps;

  for (ps = propspaces; ps; ps = ps->next) {
    if ((ps == ps->root) && (ps->type == ATTRIBUTE)) {
      extend_one_attribute_space(ps);
    }
  }
}

/* find whether object is in the property space or not */
/* return 1: if object is in the PS; 0: otherwise      */
int
find_property_space_object (propspace_ptr ps, char *obj)
{
  token_list o;
  for (o = ps->obj; o; o = o->next)
    if (strcmp(o->item, obj) == 0)
      return 1;
  return 0;
}

/* identify types for objects */
void
identify_object_types ()
{
  int obj_type;
  objtype_ptr o;
  propspace_ptr ps;
  
  for (o = objtypes; o; o = o->next) {
    obj_type = 0;
    for (ps = propspaces; ps; ps = ps->next)
      if (find_property_space_object(ps, o->name))
	obj_type = obj_type | ps->index;
    o->type = obj_type;
    // printf ("%s %d\n", o->name, o->type);
  } 
}

/* adjust property type into postive sign, since it maybe marked as negative */
void
adjust_property_type_sign ()
{
  propspace_ptr ps;
  for (ps = propspaces; ps; ps = ps->next) {
    ps->type = abs(ps->type);
  } 
}


/* return the pointer to the object name in the objtypes structure */
/* the object type is changed for "type" paramter                  */
char *
find_object_type (char *name, int *type)
{
  objtype_ptr o;

  for (o = objtypes; o; o = o->next) {
    if (strcmp(o->name, name) == 0) {
      *type = o->type;
      return o->name;
    }
  }
  fprintf(STDMSG, "cannot find object %s\n", name);
  exit(0);
}

/* add the boject type into property space */
void 
add_object_type2property_space(propspace_ptr ps, int obj_type)
{
  int i, *obj_types_ptr = ps->obj_types;
//  if (ps->type == ATTRIBUTE) {
//    ps->num_obj_types = 1;
//    ps->obj_types[0] |= obj_type;
//  }
//  else {
    for (i = 0; i < ps->num_obj_types; i++)
      if (obj_types_ptr[i] == obj_type)
	return;
    if (ps->num_obj_types == MAX_NUM_PROPERTY_OBJ_TYPE)
      do_error("exceeding maximum number of object types in property space\n");
    obj_types_ptr[ps->num_obj_types++] = obj_type;
//  }
}

/* collect object types for a property space, which will be sued 	*/
/* in the learning algorithm						*/
void
collect_property_object_types()
{
  int i, obj_type;
  propspace_ptr ps;
  token_list token;
  
  for (ps = propspaces; ps; ps = ps->next) {
    if (ps->root != ps)	
      continue;
    for (token = ps->obj; token; token = token->next) {
      find_object_type(token->item, &obj_type);
      add_object_type2property_space(ps, obj_type);
    }
  } 
}

/* add a predicate type into the predicate types list */
void
add_predicate_type (char *name, int type)
{
  predtype_ptr p;

  p = (predtype_ptr)calloc(1, sizeof(predtype_elt));
  p->name = bbstrdup(name);
  p->type = type;
  if (predtypes)	/* now add into property space list */
      p->next = predtypes;
    predtypes = p;
}

int
find_predicate_type (char *name)
{
  for (predtype_ptr p = predtypes; p; p = p->next) {
    if (strcmp(p->name, name) == 0)
      return p->type;
  }
}

predtype_ptr
locate_predicate_type (char *name)
{
  for (predtype_ptr p = predtypes; p; p = p->next) {
    if (strcmp(p->name, name) == 0)
      return p;
  }
}

/* get predicate types for evaluation functions in control.c */
void
build_predicate_types (void)
{
  int i, num_var, type;
  char *name, str[100];
  propspace_ptr ps;

  for (fact_list f = predicates; f; f = f->next) {
    name = f->item->item;
    num_var = get_predicate_variable_number(name);
    type = STATIC;
    for (i = 1; i <= num_var; i++) {
      ps = find_property_space (name, i);
      if (ps->root->type == PROPERTY) {
	type = DYNAMIC;
	break;
      }
    }
    add_predicate_type(name, type);
    if (lookup_negation_predicate (name)) {
      sprintf(str, bbun_str, name);
      add_predicate_type(str, type);
    }
  }
}

void
adjust_predicate_types ()
{
  token_list token;
  predtype_ptr p;
  for (op_list op = ops; op; op = op->next) {
    for (fact_list effect = op->effects; effect; effect = effect->next) {
      token = effect->item;
      if (strcmp(token->item, DELETE) == 0)
	token = token->next;
      p = locate_predicate_type(token->item);
      p->type = DYNAMIC;
    }
  }
}

void 
inference_type ()
{
  fprintf(STDMSG, "Performing Type Inference.....");
  build_transition_rule();
  seed_property_spaces();
  assign_transition_rule();
  assign_initial_state();
  extend_property_spaces();
  extend_attribute_spaces();
  identify_object_types();
  adjust_property_type_sign();
  fprintf(STDMSG, "completed!\n");
  collect_property_object_types();
  build_predicate_types();
  adjust_predicate_types();
#ifdef BBDEBUG
  print_property_space();
  print_predicate_types();
#endif
}

#endif










