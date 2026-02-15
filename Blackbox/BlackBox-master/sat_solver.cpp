#include <iostream>
#include <fstream>
#include <stdlib.h>
#include <stdio.h>
#include <set>
#include <vector>

// #ifdef USENAMESPACESTD
using namespace std;
// #endif

#include "zchaff/SAT.h"
#include "interface.h"
#include "utilities.h"


int
verify_solution(SAT_Manager mng)
{
    for ( int cl_idx = SAT_GetFirstClause (mng); cl_idx >= 0; 
	  cl_idx = SAT_GetNextClause(mng, cl_idx)) {
	int len = SAT_GetClauseNumLits(mng, cl_idx);
	int *lits = (int *)malloc(sizeof(int) * len + 1);
	SAT_GetClauseLits( mng, cl_idx, lits);
	int i;
	for (i=0; i< len; ++i) {
	    int v_idx = lits[i] >> 1;
	    int sign = lits[i] & 0x1;
	    int var_value = SAT_GetVarAsgnment (mng, v_idx);
	    if( (var_value == 1 && sign == 0) ||
		(var_value == 0 && sign == 1) ) break;
	}
	if (i >= len) {
	    cerr << "Verify Satisfiable solution failed, please file a bug report, thanks. " << endl;
	    return 0;
	}
    }
    return 1;
    //    cout << "Verify Solution successful. ";
}


int bb_satsolve_chaff (int numvar, int numclause, int * wff, int * soln, 
                       int maxtime, int argc, char * argv[])
{
  SAT_Manager mng = SAT_InitManager();
  int wff_idx, var_idx, result;
  set<int> clause_vars;
  set<int> clause_lits;
  // int	lits[100];
  
  //printf ("%d %d\n", numvar, numclause);
  SAT_SetNumVariables(mng, numvar); 
  wff_idx = 0;
  for (int i = 0; i < numclause; i++) {
    while ((var_idx = wff[wff_idx++]) != 0) {
      int sign = 0;
      if (var_idx < 0) { 
	sign = 1;
	var_idx = -var_idx; 
      } 
      clause_vars.insert(var_idx);
      clause_lits.insert((var_idx << 1) + sign);
    }
    if (clause_vars.size() != 0 && 
	(clause_vars.size() == clause_lits.size())) { 
      vector<int> temp;
      for (set<int>::iterator itr = clause_lits.begin(); 
	   itr != clause_lits.end(); ++itr) {
	temp.push_back (*itr);
      } 
      int * intprt;
      // Fix for some improper use of iterators
      // - HAK, Jan 2003
      intprt = & (* temp.begin());
      SAT_AddClause(mng, intprt, temp.size() );

      /*
      for (int j = 0; j < temp.size(); j++) {
	printf (" %d", temp[j]);
      }
      cout << endl; */
    }
    clause_lits.clear();
    clause_vars.clear();
  }
  //SAT_SetRandomness (mng, 10);
  //SAT_SetRandSeed (mng, -1);
  // printf ("%d %d\n", SAT_NumVariables(mng),SAT_NumClauses(mng));

  /*
  int idx = SAT_GetFirstClause(mng);
  
  do { 
    int len = SAT_GetClauseNumLits(mng, idx);
    SAT_GetClauseLits	(mng, idx, lits);
    for (int j = 0; j < len; j++) {
      int k = lits[j];
      if ((k % 2) != 0)
	 k = -((k - 1) / 2);
      else 
	k = k / 2;
      printf (" %d", k);
    }
    cout << " 0" << endl;
  } while ((idx = SAT_GetNextClause(mng, idx)) != -1);
  */
  if (maxtime > 0)
      SAT_SetTimeLimit(mng, maxtime); 
  switch(SAT_Solve(mng)) {
  case SATISFIABLE:
    if (verify_solution(mng)) {
      result= Sat;	
      for (int i = 1; i <= numvar; i++) {
	switch(SAT_GetVarAsgnment(mng, i)) {
	case 1:
	  //	  printf("%d\n", i);
	  soln[i] = 1; break;
	case 0:
	case -1:	
	  soln[i] = 0; break;
	default:
	  cerr << "Unknown variable value state"<< endl;
	  exit(4);
	}
      }
    }	
    else 
      result = Unsat;
    break;
  case UNSATISFIABLE:
    result  = Unsat;
    cout << "Instance unsatisfiable" << endl;
    break;
  case TIME_OUT:
    result  = Timeout; 
    cout << "Time out, unable to determing the satisfiablility of the instance";
    cout << endl;
    break;
  case MEM_OUT:
    result  = Failure; 
    cout << "Memory out, unable to determing the satisfiablility of the instance";
    cout << endl;
    break;
  default:
    cerr << "Unknown outcome" << endl;
    result = Failure;
  }	
  return result;
}

