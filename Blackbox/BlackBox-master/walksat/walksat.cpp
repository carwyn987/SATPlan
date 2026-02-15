/* walksat version 36 */
/* version 1 by Bram Cohen 7/93 */
/* versions 2 - 36  by Henry Kautz */

/************************************/
/* Compilation flags                */
/************************************/

/* If the constant HUGE is set, then dynamic arrays are used instead of static arrays.
   This allows very large or very small problems to be handled, without
   having to adjust the constants MAXATOM and/or MAXCLAUSE.  However, on some
   architectures (e.g. SGI) the compiled program is about 25% slower, because not
   as many optimizations can be performed. */

/* #define HUGE 1 */

/* If the constant NT is set, then the program is modified to compile under Windows NT.
   Currently, this eliminates the timing functionality. */

/* #define NT 1 */

/************************************/
/* Standard includes                */
/************************************/

#include "../interface.h"

/* Can't find header files on Sun for srandom
   (not in stdlib.h!)
   - but live with warnings, because these
   declarations break on linux! 
long random(void);
int srandom( unsigned seed);
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <sys/types.h>
#include <limits.h>
#include <signal.h>

// #ifndef WIN32
// #include <sys/times.h>
//#include <sys/time.h>
// #include <unistd.h>
// #else
// #include "../win32/adns/adns_win32.h"
// #endif

#include <sys/times.h>
#include <sys/time.h>
#include <unistd.h>

#ifndef CLK_TCK
#define CLK_TCK 60
#endif

#ifdef WIN32
#define random() rand()
#define srandom(seed) srand(seed)
#endif

/************************************/
/* Constant parameters              */
/************************************/

#define MAXATOM 100000		/* maximum possible number of atoms */

#ifdef Huge
#define STOREBLOCK 2000000	/* size of block to malloc each time */
#else
#define STOREBLOCK 2000000	/* size of block to malloc each time */
#define MAXCLAUSE 500000	/* maximum possible number of clauses */
#endif

#define TRUE 1
#define FALSE 0

#define MAXLENGTH 500           /* maximum number of literals which can be in any clause */



/************************************/
/* Internal constants               */
/************************************/

enum heuristics { RANDOM, BEST, TABU, NOVELTY, RNOVELTY };

#define NOVALUE -1
#define INIT_PARTIAL 1
#define HISTMAX 101		/* length of histogram of tail */

#define Var(CLAUSE, POSITION) (ABS(clause[CLAUSE][POSITION]))

static int scratch;
#define ABS(x) ((scratch=(x))>0?(scratch):(-scratch))

#define BIG 100000000



/************************************/
/* Main data structures             */
/************************************/

/* Atoms start at 1 */
/* Not a is recorded as -1 * a */
/* One dimensional arrays are statically allocated. */
/* Two dimensional arrays are dynamically allocated in */
/* the second dimension only.  */

int numatom;
int numclause;
int numliterals;

#ifdef Huge
int ** clause;			/* clauses to be satisfied */
				/* indexed as clause[clause_num][literal_num] */
int * size;			/* length of each clause */
int * wfalse;			/* clauses which are false */
int * lowfalse;
int * wherefalse;		/* where each clause is listed in false */
int * numtruelit;		/* number of true literals in each clause */
#else
int * clause[MAXCLAUSE];	/* clauses to be satisfied */
				/* indexed as clause[clause_num][literal_num] */
int size[MAXCLAUSE];		/* length of each clause */
int wfalse[MAXCLAUSE];		/* clauses which are false */
int lowfalse[MAXCLAUSE];
int wherefalse[MAXCLAUSE];	/* where each clause is listed in false */
int numtruelit[MAXCLAUSE];	/* number of true literals in each clause */
#endif

int *occurence[2*MAXATOM+1];	/* where each literal occurs */
				/* indexed as occurence[literal+MAXATOM][occurence_num] */

int numoccurence[2*MAXATOM+1];	/* number of times each literal occurs */


int atom[MAXATOM+1];		/* value of each atom */ 
int lowatom[MAXATOM+1];
int solution[MAXATOM+1];

int changed[MAXATOM+1];		/* step at which atom was last flipped */

int breakcount[MAXATOM+1];	/* number of clauses that become unsat if var if flipped */
int makecount[MAXATOM+1];	/* number of clauses that become sat if var if flipped */

int numfalse;			/* number of false clauses */

/************************************/
/* Global flags and parameters      */
/************************************/

int abort_flag;

int heuristic = BEST;		/* heuristic to be used */
int numerator = NOVALUE;	/* make random flip with numerator/denominator frequency */
int denominator = 100;		
int tabu_length;		/* length of tabu list */

long int numflip;		/* number of changes so far */
long int numnullflip;		/*  number of times a clause was picked, but no  */
				/*  variable from it was flipped  */
int numrun = 10;
int WS_cutoff = 100000;
int base_cutoff = 100000;
int target = 0;
int numtry = 0;			/* total attempts at solutions */
int numsol = NOVALUE;		/* stop after this many tries succeeds */
int superlinear = FALSE;

int makeflag = FALSE;		/* set to true by heuristics that require the make values to be calculated */

/* Histogram of tail */

long int tailhist[HISTMAX];	/* histogram of num unsat in tail of run */
long histtotal;
int tail = 3;
int tail_start_flip;

/* Printing options */

int printonlysol = FALSE;
int printsolcnf = FALSE;
int printfalse = FALSE;
int printlow = FALSE;
int printhist = FALSE;
int printtrace = FALSE;
int trace_assign = FALSE;

/* Initialization options */

char initfile[100] = { 0 };
int initoptions = FALSE;

/* Randomization */

extern int seed;			/* seed for random */
extern struct timeval tv;
// extern struct timezone tzp;

/* Statistics */

double expertime;
long flips_this_solution;
int lowbad;		/* lowest number of bad clauses during try */
long int totalflip = 0;		/* total number of flips in all tries so far */
long int totalsuccessflip = 0;	/* total number of flips in all tries which succeeded so far */
int WS_numsuccesstry = 0;		/* total found solutions */

extern long x;
long WS_integer_sum_x = 0;
double WS_sum_x = 0.0;
double WS_sum_x_squared = 0.0;
extern double mean_x;
extern double second_moment_x;
extern double variance_x;
extern double std_dev_x;
extern double std_error_mean_x;
double seconds_per_flip;
extern int r;
int WS_sum_r = 0;
double WS_sum_r_squared = 0.0;
extern double mean_r;
extern double variance_r;
extern double std_dev_r;
extern double std_error_mean_r;

double avgfalse;
double sumfalse;
double sumfalse_squared;
double second_moment_avgfalse, variance_avgfalse, std_dev_avgfalse, ratio_avgfalse;
// double std_dev_avgfalse;
double f;
double sample_size;

double sum_avgfalse = 0.0;
double sum_std_dev_avgfalse = 0.0;
double mean_avgfalse;
double mean_std_dev_avgfalse;
int number_sampled_runs = 0;
double ratio_mean_avgfalse;

double suc_sum_avgfalse = 0.0;
double suc_sum_std_dev_avgfalse = 0.0;
double suc_mean_avgfalse;
double suc_mean_std_dev_avgfalse;
int suc_number_sampled_runs = 0;
double suc_ratio_mean_avgfalse;

double nonsuc_sum_avgfalse = 0.0;
double nonsuc_sum_std_dev_avgfalse = 0.0;
double nonsuc_mean_avgfalse;
double nonsuc_mean_std_dev_avgfalse;
int nonsuc_number_sampled_runs = 0;
double nonsuc_ratio_mean_avgfalse;

/* Hamming calcualations */

char hamming_target_file[512] = { 0 };
char hamming_data_file[512] = { 0 };
int hamming_sample_freq;
int hamming_flag = FALSE;
int hamming_distance;
int hamming_target[MAXATOM+1];
void read_hamming_file(char initfile[]);
void open_hamming_data(char initfile[]);
int calc_hamming_dist(int atom[], int hamming_target[], int numatom);
FILE * hamming_fp;

/* Noise level */
int samplefreq = 1;

/************************************/
/* Forward declarations             */
/************************************/

void parse_parameters(int argc,char *argv[]);
void print_parameters(int argc, char * argv[]);

int pickrandom(void);
int pickbest(void);
int picktabu(void);
int picknovelty(void);
int pickrnovelty(void);
char * heuristic_names[] = { "random", "best", "tabu", "novelty", "rnovelty" };
static int (*pickcode[])(void) =
      {pickrandom, pickbest, picktabu, picknovelty, pickrnovelty};

// double WS_elapsed_seconds(void);
int countunsat(void);
void scanone(int argc, char *argv[], int i, int *varptr);
void scanonef(int argc, char *argv[], int i, float *varptr);
void init(char initfile[], int initoptions);

void initprob(int numvararg, int numclausearg, int * wff);
void flipatom(int toflip);           /* changes the assignment of the given literal */

void print_false_clauses( int lowbad);
void save_false_clauses( int lowbad);
void print_low_assign( int lowbad);
void save_low_assign(void);
void WS_save_solution(void);

void print_current_assign(void);
void handle_interrupt(int sig);

long super(int i);


void print_statistics_header(void);
void initialize_statistics(void);
void update_statistics_start_try(void);
void print_statistics_start_flip(void);
void update_and_print_statistics_end_try(void);
void update_statistics_end_flip(void);
void WS_print_statistics_final(void);
void print_sol_cnf(void);

/************************************/
/* Main                             */
/************************************/

void reset_static_vars(void)
{
    numrun = 10;
    WS_cutoff = 100000;
    base_cutoff = 100000;
    target = 0;
    numtry = 0;			
    numsol = 1;
    superlinear = FALSE;
    makeflag = FALSE;		
    tail = 3;
    printonlysol = FALSE;
    printsolcnf = FALSE;
    printfalse = FALSE;
    printlow = FALSE;
    printhist = FALSE;
    printtrace = FALSE;
    trace_assign = FALSE;
    initfile[0] = 0;
    initoptions = FALSE;
    totalflip = 0;		
    totalsuccessflip = 0;	
    WS_numsuccesstry = 0;		
    WS_integer_sum_x = 0;
    WS_sum_x = 0.0;
    WS_sum_x_squared = 0.0;
    WS_sum_r = 0;
    WS_sum_r_squared = 0.0;
    sum_avgfalse = 0.0;
    sum_std_dev_avgfalse = 0.0;
    number_sampled_runs = 0;
    suc_sum_avgfalse = 0.0;
    suc_sum_std_dev_avgfalse = 0.0;
    suc_number_sampled_runs = 0;
    nonsuc_sum_avgfalse = 0.0;
    nonsuc_sum_std_dev_avgfalse = 0.0;
    nonsuc_number_sampled_runs = 0;
    hamming_target_file[0] = 0;
    hamming_data_file[0] = 0;
    hamming_flag = FALSE;
    samplefreq = 1;
}



int bb_satsolve_walksat (int numvararg, int numclausearg, int * wff, 
                         int * soln, int maxtime, int argc, char * argv[] )
{
    int i;


    fprintf(STDMSG, "Invoking solver walksat version 36\n");


    reset_static_vars();



    gettimeofday(&tv,0);
    seed = (( tv.tv_sec & 0177 ) * 1000000) + tv.tv_usec;
    parse_parameters(argc, argv);
    srandom(seed);
    print_parameters(argc, argv);
    initprob(numvararg, numclausearg, wff);
    initialize_statistics();
    print_statistics_header();
    /* signal(SIGINT, (void *) handle_interrupt); */
    abort_flag = FALSE;
    elapsed_seconds();

    while (! abort_flag && WS_numsuccesstry < numsol && numtry < numrun) {
	numtry++;
	init(initfile, initoptions);
	update_statistics_start_try();
	numflip = 0;
	  
	if (superlinear) WS_cutoff = base_cutoff * super(numtry);

	while((numfalse > target) && (numflip < WS_cutoff) && !(abort_flag |= bb_limitp(Walksat_Rate))) {
	    print_statistics_start_flip();
	    numflip++;
	    flipatom((pickcode[heuristic])());
	    update_statistics_end_flip();
	}
	update_and_print_statistics_end_try();
    }
    expertime = elapsed_seconds();
    WS_print_statistics_final();

    if (WS_numsuccesstry){
	for (i=1; i<=numatom; i++)
	    soln[i] = solution[i];
	return Sat;
    }
    else return Timeout;
}



void parse_parameters(int argc,char *argv[])
{
  int i;
  int temp;
  float tempf;

  for (i=1;i < argc;i++)
    {
      if (strcmp(argv[i],"-seed") == 0)
	scanone(argc,argv,++i,&seed);
      else if (strcmp(argv[i],"-hist") == 0)
	printhist = TRUE;
      else if (strcmp(argv[i],"-cutoff") == 0)
	scanone(argc,argv,++i,&WS_cutoff);
      else if (strcmp(argv[i],"-random") == 0)
	heuristic = RANDOM;
      else if (strcmp(argv[i],"-novelty") == 0){
	heuristic = NOVELTY;
	makeflag = TRUE;
      }
      else if (strcmp(argv[i],"-rnovelty") == 0){
	heuristic = RNOVELTY;
	makeflag = TRUE;
      }
      else if (strcmp(argv[i],"-best") == 0)
	heuristic = BEST;

      else if (strcmp(argv[i],"-noise") == 0){
	scanonef(argc,argv,++i,&tempf);
	if (i < argc-1 && sscanf(argv[i+1],"%i",&temp)==1){
	  denominator = temp;
	  numerator = (int) tempf;
	  i++;
	}
	else {
	    if (tempf > 1.0) {
		numerator = (int) tempf;
		denominator = 100;
	    }
	    else {
		denominator = 100;
		numerator = (int)(tempf * 100.0);
	    }
	}
	if (numerator < 0) numerator = 0;
	if (numerator > 100) numerator = 100;
      }

      else if (strcmp(argv[i],"-init") == 0  && i < argc-1)
	sscanf(argv[++i], " %s", initfile);
      else if (strcmp(argv[i],"-hamming") == 0  && i < argc-3){
	sscanf(argv[++i], " %s", hamming_target_file);
	sscanf(argv[++i], " %s", hamming_data_file);
	sscanf(argv[++i], " %i", &hamming_sample_freq);
	hamming_flag = TRUE;
	numrun = 1;
      }
      else if (strcmp(argv[i],"-partial") == 0)
	initoptions = INIT_PARTIAL;
      else if (strcmp(argv[i],"-super") == 0)
	superlinear = TRUE;
      else if (strcmp(argv[i],"-tries") == 0)
	scanone(argc,argv,++i,&numrun);
      else if (strcmp(argv[i],"-restart") == 0)
	scanone(argc,argv,++i,&numrun);
      else if (strcmp(argv[i],"-target") == 0)
	scanone(argc,argv,++i,&target);
      else if (strcmp(argv[i],"-tail") == 0)
	scanone(argc,argv,++i,&tail);
      else if (strcmp(argv[i],"-sample") == 0)
	scanone(argc,argv,++i,&samplefreq);
      else if (strcmp(argv[i],"-tabu") == 0)
	{
	  scanone(argc,argv,++i,&tabu_length);
	  heuristic = TABU;
	}
      else if (strcmp(argv[i],"-low") == 0)
	printlow = TRUE;
      else if (strcmp(argv[i],"-sol") == 0)
	{
	  printonlysol = TRUE;
	  printlow = TRUE;
	}
      else if (strcmp(argv[i],"-solcnf") == 0)
	{
	  printsolcnf = TRUE;
	  if (numsol == NOVALUE) numsol = 1;
	}
      else if (strcmp(argv[i],"-bad") == 0)
	printfalse = TRUE;
      else if (strcmp(argv[i],"-numsol") == 0)
	scanone(argc,argv,++i,&numsol);
      else if (strcmp(argv[i],"-trace") == 0)
	scanone(argc,argv,++i,&printtrace);
      else if (strcmp(argv[i],"-assign") == 0){
	scanone(argc,argv,++i,&printtrace);
	trace_assign = TRUE;
      }
      else 
	{
	  if (strcmp(argv[i],"-help")!=0 && strcmp(argv[i],"-h")!=0 )
	    fprintf(STDMSG, "Bad argument %s\n", argv[i]);
	  fprintf(STDMSG, "Options for walksat solver are:\n");
	  fprintf(STDMSG, "  -seed N -cutoff N\n");
	  fprintf(STDMSG, "  -restart N (same as -tries N)\n");
	  fprintf(STDMSG, "  -noise F (where 0.0 <= F <= 1.0)\n");
	  fprintf(STDMSG, "     -noise N M (same as -noise N/M)\n");
	  fprintf(STDMSG, "     -noise N (where N > 1, same as -noise N/100)\n");
	  fprintf(STDMSG, "  -numsol N = stop after finding N solutions\n");
	  fprintf(STDMSG, "  -init FILE = set vars not included in FILE to false\n");
	  fprintf(STDMSG, "  -target N (stop if reach N bad clauses)\n");
	  fprintf(STDMSG, "  -partial FILE = set vars not included in FILE randomly\n");
	  fprintf(STDMSG, "Heuristics:\n");
	  fprintf(STDMSG, "  -random -best -tabu N -novelty -rnovelty\n");
	  fprintf(STDMSG, "  -noise N or -noise N M (default M = 100)\n");
	  fprintf(STDMSG, "Printing:\n");
	  fprintf(STDMSG, "  -hamming TARGET_FILE DATA_FILE SAMPLE_FREQUENCY\n");
	  fprintf(STDMSG, "  -trace N = print statistics every N flips\n");
	  fprintf(STDMSG, "  -assign N = print assignments at flip N, 2N, ...\n");
	  fprintf(STDMSG, "  -sol = print satisfying assignments\n");
	  fprintf(STDMSG, "  -low = print lowest assignment each try\n");
	  fprintf(STDMSG, "  -bad = print unsat clauses each try\n");
	  fprintf(STDMSG, "  -tail N = assume tail begins at nvars*N\n");
	  fprintf(STDMSG, "  -solcnf = print sat assign in cnf format, and exit\n");
	  fprintf(STDMSG, "  -sample N = sample noise level every N flips\n");
	  exit(-1);
	}
    }
  base_cutoff = WS_cutoff;
  if (numsol==NOVALUE || numsol>numrun) numsol = numrun;
  if (numerator==NOVALUE){
    switch(heuristic) {
    case BEST:
    case NOVELTY:
    case RNOVELTY:
      numerator = 50;
      break;
    default:
      numerator = 0;
      break;
    }
  }
}


void print_parameters(int argc, char * argv[])
{
  int i;

#ifdef Huge
  fprintf(STDMSG, "walksat version 36 (Huge)\n");
#else
  fprintf(STDMSG, "walksat version 36\n");
#endif
  fprintf(STDMSG, "command line =");
  for (i=0;i < argc;i++){
    fprintf(STDMSG, " %s", argv[i]);
  }
  fprintf(STDMSG, "\n");
  fprintf(STDMSG, "seed = %i\n",seed);
  fprintf(STDMSG, "cutoff = %i\n",WS_cutoff);
  fprintf(STDMSG, "tries = %i\n",numrun);

  fprintf(STDMSG, "heuristic = ");
  switch(heuristic)
    {
    case TABU:
      fprintf(STDMSG, "tabu %d", tabu_length);
      break;
    default:
      fprintf(STDMSG, "%s", heuristic_names[heuristic]);
      break;
    }
  if (numerator>0){
    fprintf(STDMSG, ", noise %d / %d", numerator, denominator);
  }
  fprintf(STDMSG, "\n");
}

void print_statistics_header(void)
{
    fprintf(STDMSG, "numatom = %i, numclause = %i, numliterals = %i\n",numatom,numclause,numliterals);
    fprintf(STDMSG, "wff read in\n\n");
    fprintf(STDMSG, "    lowest     final       avg     noise     noise     total                 avg        mean        mean\n");
    fprintf(STDMSG, "    #unsat    #unsat     noise   std dev     ratio     flips              length       flips       flips\n");
    fprintf(STDMSG, "      this      this      this      this      this      this   success   success       until         std\n");
    fprintf(STDMSG, "       try       try       try       try       try       try      rate     tries      assign         dev\n\n");

    fflush(stdout);

}

void initialize_statistics(void)
{
    x = 0; r = 0;
    if (hamming_flag) {
	read_hamming_file(hamming_target_file);
	open_hamming_data(hamming_data_file);
    }
    tail_start_flip = tail * numatom;
    fprintf(STDMSG, "tail starts after flip = %i\n", tail_start_flip);
    numnullflip = 0;


}

void update_statistics_start_try(void)
{
    int i;

    lowbad = numfalse;

    sample_size = 0;
    sumfalse = 0.0;
    sumfalse_squared = 0.0;

    for (i=0; i<HISTMAX; i++)
	tailhist[i] = 0;
    if (tail_start_flip == 0){
	tailhist[numfalse < HISTMAX ? numfalse : HISTMAX - 1] ++;
    }
	      
    if (printfalse) save_false_clauses(lowbad);
    if (printlow) save_low_assign();
}

void print_statistics_start_flip(void)
{
    if (printtrace && (numflip % printtrace == 0)){
	fprintf(STDMSG, " %9i %9i                     %9li\n", lowbad,numfalse,numflip);
	if (trace_assign)
	    print_current_assign();
	fflush(stdout);
    }
}


void update_and_print_statistics_end_try(void)
{
    int i;
    int j;

    totalflip += numflip;
    x += numflip;
    r ++;

    if (sample_size > 0){
	avgfalse = sumfalse/sample_size;
	second_moment_avgfalse = sumfalse_squared / sample_size;
	variance_avgfalse = second_moment_avgfalse - (avgfalse * avgfalse);
	if (sample_size > 1) { variance_avgfalse = (variance_avgfalse * sample_size)/(sample_size - 1); }
	std_dev_avgfalse = sqrt(variance_avgfalse);

	ratio_avgfalse = avgfalse / std_dev_avgfalse;

	sum_avgfalse += avgfalse;
	sum_std_dev_avgfalse += std_dev_avgfalse;
	number_sampled_runs += 1;

	if (numfalse == 0){
	    suc_number_sampled_runs += 1;
	    suc_sum_avgfalse += avgfalse;
	    suc_sum_std_dev_avgfalse += std_dev_avgfalse;
	}
	else {
	    nonsuc_number_sampled_runs += 1;
	    nonsuc_sum_avgfalse += avgfalse;
	    nonsuc_sum_std_dev_avgfalse += std_dev_avgfalse;
	}
    }
    else{
	avgfalse = 0;
	variance_avgfalse = 0;
	std_dev_avgfalse = 0;
	ratio_avgfalse = 0;
    }

    if(numfalse == 0){

	WS_save_solution();
	WS_numsuccesstry++;

	totalsuccessflip += numflip;
	WS_integer_sum_x += x;
	WS_sum_x = (double) WS_integer_sum_x;
	WS_sum_x_squared += ((double)x)*((double)x);
	mean_x = WS_sum_x / WS_numsuccesstry;
	if (WS_numsuccesstry > 1){
	    second_moment_x = WS_sum_x_squared / WS_numsuccesstry;
	    variance_x = second_moment_x - (mean_x * mean_x);
	    /* Adjustment for small small sample size */
	    variance_x = (variance_x * WS_numsuccesstry)/(WS_numsuccesstry - 1);
	    std_dev_x = sqrt(variance_x);
	    std_error_mean_x = std_dev_x / sqrt((double)WS_numsuccesstry);
	}
	WS_sum_r += r;
	mean_r = ((double)WS_sum_r)/WS_numsuccesstry;
	WS_sum_r_squared += ((double)r)*((double)r);

	x = 0;
	r = 0;
    }

    fprintf(STDMSG, " %9i %9i %9.2f %9.2f %9.2f %9li %9i",
	   lowbad,numfalse,avgfalse, std_dev_avgfalse,ratio_avgfalse,numflip, ((WS_numsuccesstry*100)/numtry));
    if (WS_numsuccesstry > 0){
	fprintf(STDMSG, " %9i", (int)(totalsuccessflip/WS_numsuccesstry));
	fprintf(STDMSG, " %11.2f", mean_x);
	if (WS_numsuccesstry > 1){
	    fprintf(STDMSG, " %11.2f", std_dev_x);
	}
    }
    fprintf(STDMSG, "\n");

    if (printhist){
	fprintf(STDMSG, "histogram: ");
	for (j=HISTMAX-1; tailhist[j] == 0; j--);
	for (i=0; i<=j; i++){
	    fprintf(STDMSG, " %i(%i)", (int)(tailhist[i]), i);
	    if ((i+1) % 10 == 0) fprintf(STDMSG, "\n           ");
	}
	if (j==HISTMAX-1) fprintf(STDMSG, " +++");
	fprintf(STDMSG, "\n");
    }

    if (numfalse>0 && printfalse)
	print_false_clauses(lowbad);
    if (printlow && (!printonlysol || numfalse >= target))
	print_low_assign(lowbad);

    if(numfalse == 0 && countunsat() != 0){
	fprintf(STDMSG, "Program error, verification of solution fails!\n");
	exit(-1);
    }

    fflush(stdout);
}

void update_statistics_end_flip(void)
{
    if (numfalse < lowbad){
	lowbad = numfalse;
	if (printfalse) save_false_clauses(lowbad);
	if (printlow) save_low_assign();
    }
    if (numflip >= tail_start_flip){
	tailhist[(numfalse < HISTMAX) ? numfalse : (HISTMAX - 1)] ++;
	if ((numflip % samplefreq) == 0){
	  sumfalse += numfalse;
	  sumfalse_squared += numfalse * numfalse;
	  sample_size ++;
	}
    }
}

void WS_print_statistics_final(void)
{
    seconds_per_flip = expertime / totalflip;
    fprintf(STDMSG, "\ntotal elapsed seconds = %f\n", expertime);
    fprintf(STDMSG, "average flips per second = %ld\n", (long)(totalflip/expertime));
    if (heuristic == TABU)
	fprintf(STDMSG, "proportion null flips = %f\n", ((double)numnullflip)/totalflip);
    fprintf(STDMSG, "number solutions found = %d\n", WS_numsuccesstry);
    fprintf(STDMSG, "final success rate = %f\n", ((double)WS_numsuccesstry * 100.0)/numtry);
    fprintf(STDMSG, "average length successful tries = %li\n", WS_numsuccesstry ? (totalsuccessflip/WS_numsuccesstry) : 0);
    if (WS_numsuccesstry > 0)
	{
	    fprintf(STDMSG, "mean flips until assign = %f\n", mean_x);
	    if (WS_numsuccesstry>1){
		fprintf(STDMSG, "  variance = %f\n", variance_x);
		fprintf(STDMSG, "  standard deviation = %f\n", std_dev_x);
		fprintf(STDMSG, "  standard error of mean = %f\n", std_error_mean_x);
	    }
	    fprintf(STDMSG, "mean seconds until assign = %f\n", mean_x * seconds_per_flip);
	    if (WS_numsuccesstry>1){
		fprintf(STDMSG, "  variance = %f\n", variance_x * seconds_per_flip * seconds_per_flip);
		fprintf(STDMSG, "  standard deviation = %f\n", std_dev_x * seconds_per_flip);
		fprintf(STDMSG, "  standard error of mean = %f\n", std_error_mean_x * seconds_per_flip);
	    }
	    fprintf(STDMSG, "mean restarts until assign = %f\n", mean_r);
	    if (WS_numsuccesstry>1){
		variance_r = (WS_sum_r_squared / WS_numsuccesstry) - (mean_r * mean_r);
		if (WS_numsuccesstry > 1) variance_r = (variance_r * WS_numsuccesstry)/(WS_numsuccesstry - 1);	   
		std_dev_r = sqrt(variance_r);
		std_error_mean_r = std_dev_r / sqrt((double)WS_numsuccesstry);
		fprintf(STDMSG, "  variance = %f\n", variance_r);
		fprintf(STDMSG, "  standard deviation = %f\n", std_dev_r);
		fprintf(STDMSG, "  standard error of mean = %f\n", std_error_mean_r);
	    }
	}

    if (number_sampled_runs){
      mean_avgfalse = sum_avgfalse / number_sampled_runs;
      mean_std_dev_avgfalse = sum_std_dev_avgfalse / number_sampled_runs;
      ratio_mean_avgfalse = mean_avgfalse / mean_std_dev_avgfalse;

      if (suc_number_sampled_runs){
	  suc_mean_avgfalse = suc_sum_avgfalse / suc_number_sampled_runs;
	  suc_mean_std_dev_avgfalse = suc_sum_std_dev_avgfalse / suc_number_sampled_runs;
	  suc_ratio_mean_avgfalse = suc_mean_avgfalse / suc_mean_std_dev_avgfalse;
      }
      else {
	  suc_mean_avgfalse = 0;
	  suc_mean_std_dev_avgfalse = 0;
	  suc_ratio_mean_avgfalse = 0;
      }

      if (nonsuc_number_sampled_runs){
	  nonsuc_mean_avgfalse = nonsuc_sum_avgfalse / nonsuc_number_sampled_runs;
	  nonsuc_mean_std_dev_avgfalse = nonsuc_sum_std_dev_avgfalse / nonsuc_number_sampled_runs;
	  nonsuc_ratio_mean_avgfalse = nonsuc_mean_avgfalse / nonsuc_mean_std_dev_avgfalse;
      }
      else {
	  nonsuc_mean_avgfalse = 0;
	  nonsuc_mean_std_dev_avgfalse = 0;
	  nonsuc_ratio_mean_avgfalse = 0;
      }

      fprintf(STDMSG, "final noise level statistics\n");
      fprintf(STDMSG, "    statistics over all runs:\n");
      fprintf(STDMSG, "      overall mean average noise level = %f\n", mean_avgfalse);
      fprintf(STDMSG, "      overall mean noise std deviation = %f\n", mean_std_dev_avgfalse);
      fprintf(STDMSG, "      overall ratio mean noise to mean std dev = %f\n", ratio_mean_avgfalse);
      fprintf(STDMSG, "    statistics on successful runs:\n");
      fprintf(STDMSG, "      successful mean average noise level = %f\n", suc_mean_avgfalse);
      fprintf(STDMSG, "      successful mean noise std deviation = %f\n", suc_mean_std_dev_avgfalse);
      fprintf(STDMSG, "      successful ratio mean noise to mean std dev = %f\n", suc_ratio_mean_avgfalse);
      fprintf(STDMSG, "    statistics on nonsuccessful runs:\n");
      fprintf(STDMSG, "      nonsuccessful mean average noise level = %f\n", nonsuc_mean_avgfalse);
      fprintf(STDMSG, "      nonsuccessful mean noise std deviation = %f\n", nonsuc_mean_std_dev_avgfalse);
      fprintf(STDMSG, "      nonsuccessful ratio mean noise to mean std dev = %f\n", nonsuc_ratio_mean_avgfalse);
    }

    if (hamming_flag){
	fclose(hamming_fp);
	fprintf(STDMSG, "Final distance to hamming target = %i\n", calc_hamming_dist(atom, hamming_target, numatom));
	fprintf(STDMSG, "Hamming distance data stored in %s\n", hamming_data_file);
    }

    if (WS_numsuccesstry > 0){
	fprintf(STDMSG, "ASSIGNMENT FOUND\n");
	if(printsolcnf == TRUE) print_sol_cnf();
    }
    else
	fprintf(STDMSG, "ASSIGNMENT NOT FOUND\n");

}


long super(int i)
{
    long power;
    int k;

    if (i<=0){
	fprintf(STDMSG, "bad argument super(%d)\n", i);
	exit(1);
    }
    /* let 2^k be the least power of 2 >= (i+1) */
    k = 1;
    power = 2;
    while (power < (i+1)){
	k += 1;
	power *= 2;
    }
    if (power == (i+1)) return (power/2);
    return (super(i - (power/2) + 1));
}

void handle_interrupt(int sig)
{
    if (abort_flag) exit(-1);
    abort_flag = TRUE;
}

void scanone(int argc, char *argv[], int i, int *varptr)
{
    if (i>=argc || sscanf(argv[i],"%i",varptr)!=1){
	fprintf(STDMSG, "Bad argument %s\n", i<argc ? argv[i] : argv[argc-1]);
	exit(-1);
    }
}

void scanonef(int argc, char *argv[], int i, float *varptr)
{
    if (i>=argc || sscanf(argv[i],"%f",varptr)!=1){
	fprintf(STDMSG, "Bad argument %s\n", i<argc ? argv[i] : argv[argc-1]);
	exit(-1);
    }
}


int calc_hamming_dist(int atom[], int hamming_target[], int numatom)
{
    int i;
    int dist = 0;
    
    for (i=1; i<=numatom; i++){
	if (atom[i] != hamming_target[i]) dist++;
    }
    return dist;
}

void open_hamming_data(char initfile[])
{
    if ((hamming_fp = fopen(initfile, "w")) == NULL){
	fprintf(STDMSG, "Cannot open %s for output\n", initfile);
	exit(1);
    }
}


void read_hamming_file(char initfile[])
{
    int i;			/* loop counter */
    FILE * infile;
    int lit;    

    fprintf(STDMSG, "loading hamming target file %s ...", initfile);

    if ((infile = fopen(initfile, "r")) == NULL){
	fprintf(STDMSG, "Cannot open %s\n", initfile);
	exit(1);
    }
    i=0;
    for(i = 1;i < numatom+1;i++)
      hamming_target[i] = 0;

    while (fscanf(infile, " %d", &lit)==1){
	if (ABS(lit)>numatom){
	    fprintf(STDMSG, "Bad hamming file %s\n", initfile);
	    exit(1);
	}
	if (lit>0) hamming_target[lit]=1;
    }
    fprintf(STDMSG, "done\n");
}


void init(char initfile[], int initoptions)
{
    int i;
    int j;
    int thetruelit;
    FILE * infile;
    int lit;

    for(i = 0;i < numclause;i++)
      numtruelit[i] = 0;
    numfalse = 0;

    for(i = 1;i < numatom+1;i++)
      {
	  changed[i] = -BIG;
	  breakcount[i] = 0;
	  makecount[i] = 0;
      }

    if (initfile[0] && initoptions!=INIT_PARTIAL){
	for(i = 1;i < numatom+1;i++)
	  atom[i] = 0;
    }
    else {
	for(i = 1;i < numatom+1;i++)
	  atom[i] = random()%2;
    }

    if (initfile[0]){
	if ((infile = fopen(initfile, "r")) == NULL){
	    fprintf(STDMSG, "Cannot open %s\n", initfile);
	    exit(1);
	}
	i=0;
	while (fscanf(infile, " %d", &lit)==1){
	    i++;
	    if (ABS(lit)>numatom){
		fprintf(STDMSG, "Bad init file %s\n", initfile);
		exit(1);
	    }
	    if (lit<0) atom[-lit]=0;
	    else atom[lit]=1;
	}
	if (i==0){
	    fprintf(STDMSG, "Bad init file %s\n", initfile);
	    exit(1);
	}
	fclose(infile);
	/* fprintf(STDMSG, "read %d values\n", i); */
    }

    /* Initialize breakcount and makecount in the following: */
    for(i = 0;i < numclause;i++)
      {
	  for(j = 0;j < size[i];j++)
	    {
		if((clause[i][j] > 0) == atom[ABS(clause[i][j])])
		  {
		      numtruelit[i]++;
		      thetruelit = clause[i][j];
		  }
	    }
	  if(numtruelit[i] == 0)
	    {
		wherefalse[i] = numfalse;
		wfalse[numfalse] = i;
		numfalse++;
		for(j = 0;j < size[i];j++){
		  makecount[ABS(clause[i][j])]++;
		}
	    }
	  else if (numtruelit[i] == 1)
	    {
		breakcount[ABS(thetruelit)]++;
	    }
      }
    if (hamming_flag){
	hamming_distance = calc_hamming_dist(atom, hamming_target, numatom);
	fprintf(hamming_fp, "0 %i\n", hamming_distance);
    }
}

void
print_false_clauses(int lowbad)
{
    int i, j;
    int cl;

    fprintf(STDMSG, "Unsatisfied clauses:\n");
    for (i=0; i<lowbad; i++){
	cl = lowfalse[i];
	for (j=0; j<size[cl]; j++){
	    fprintf(STDMSG, "%d ", clause[cl][j]);
	}
	fprintf(STDMSG, "0\n");
    }
    fprintf(STDMSG, "End unsatisfied clauses\n");
}

void
save_false_clauses( int lowbad)
{
    int i;

    for (i=0; i<lowbad; i++)
      lowfalse[i] = wfalse[i];
}

void initprob(int numvararg, int numclausearg, int * wff)
{
    int i;			/* loop counter */
    int j;			/* another loop counter */
    int *storeptr;
    int freestore;
    int lit;

    numatom = numvararg;
    numclause = numclausearg;

    if(numatom > MAXATOM)
      {
	  fprintf(STDMSG,"ERROR - too many atoms\n");
	  exit(-1);
      }

#ifdef Huge
    clause = (int **) malloc(sizeof(int *)*(numclause+1));
    size = (int *) malloc(sizeof(int)*(numclause+1));
    wfalse = (int *) malloc(sizeof(int)*(numclause+1));
    lowfalse = (int *) malloc(sizeof(int)*(numclause+1));
    wherefalse = (int *) malloc(sizeof(int)*(numclause+1));
    numtruelit = (int *) malloc(sizeof(int)*(numclause+1));
#else
    if(numclause > MAXCLAUSE)                     
      {                                      
	  fprintf(STDMSG,"ERROR - too many clauses\n"); 
	  exit(-1);                              
      }                                        
#endif
    freestore = 0;
    numliterals = 0;
    for(i = 0;i < 2*MAXATOM+1;i++)
      numoccurence[i] = 0;
    for(i = 0;i < numclause;i++)
      {
	  size[i] = -1;
	  if (freestore < MAXLENGTH)
	    {
		storeptr = (int *) malloc( sizeof(int) * STOREBLOCK );
		freestore = STOREBLOCK;
		fprintf(STDMSG,"allocating memory...\n");
	    }
	  clause[i] = storeptr;
	  do
	    {
		size[i]++;
		if(size[i] > MAXLENGTH)
		  {
		      fprintf(STDMSG, "ERROR - clause too long\n");
		      exit(-1);
		  }
		lit = *(wff++);
		if(lit != 0)
		  {
		      *(storeptr++) = lit; /* clause[i][size[i]] = j; */
		      freestore--;
		      numliterals++;
		      numoccurence[lit+MAXATOM]++;
		  }
	    }
	  while(lit != 0);
      }
    if(size[0] == 0)
      {
	  fprintf(STDMSG,"ERROR - incorrect problem format or extraneous characters\n");
	  exit(-1);
      }

    for(i = 0;i < 2*MAXATOM+1;i++)
      {
	  if (freestore < numoccurence[i])
	    {
		storeptr = (int *) malloc( sizeof(int) * STOREBLOCK );
		freestore = STOREBLOCK;
		fprintf(STDMSG,"allocating memory...\n");
	    }
	  occurence[i] = storeptr;
	  freestore -= numoccurence[i];
	  storeptr += numoccurence[i];
	  numoccurence[i] = 0;
      }

    for(i = 0;i < numclause;i++)
      {
	  for(j = 0;j < size[i];j++)
	    {
		occurence[clause[i][j]+MAXATOM]
		  [numoccurence[clause[i][j]+MAXATOM]] = i;
		numoccurence[clause[i][j]+MAXATOM]++;
	    }
      }
}


void flipatom(int toflip)
{
    int i, j;			/* loop counter */
    int toenforce;		/* literal to enforce */
    register int cli;
    register int lit;
    int numocc;
    register int sz;
    register int * litptr;
    int * occptr;

    /* fprintf(STDMSG, "flipping %i\n", toflip); */

    if (toflip == NOVALUE){
	numnullflip++;
	return;
    }

    changed[toflip] = numflip;
    if(atom[toflip] > 0)
      toenforce = -toflip;
    else
      toenforce = toflip;
    atom[toflip] = 1-atom[toflip];

    if (hamming_flag){
	if (atom[toflip] == hamming_target[toflip])
	  hamming_distance--;
	else
	  hamming_distance++;
	if ((numflip % hamming_sample_freq) == 0)
	  fprintf(hamming_fp, "%li %i\n", numflip, hamming_distance);
    }
    
    numocc = numoccurence[MAXATOM-toenforce];
    occptr = occurence[MAXATOM-toenforce];
    for(i = 0; i < numocc ;i++)
      {
	  /* cli = occurence[MAXATOM-toenforce][i]; */
	  cli = *(occptr++);

	  if (--numtruelit[cli] == 0){
	      wfalse[numfalse] = cli;
	      wherefalse[cli] = numfalse;
	      numfalse++;
	      /* Decrement toflip's breakcount */
	      breakcount[toflip]--;

	      if (makeflag){
		/* Increment the makecount of all vars in the clause */
		sz = size[cli];
		litptr = clause[cli];
		for (j=0; j<sz; j++){
		  /* lit = clause[cli][j]; */
		  lit = *(litptr++);
		  makecount[ABS(lit)]++;
		}
	      }
	  }
	  else if (numtruelit[cli] == 1){
	      /* Find the lit in this clause that makes it true, and inc its breakcount */
	      sz = size[cli];
	      litptr = clause[cli];
	      for (j=0; j<sz; j++){
		  /* lit = clause[cli][j]; */
		  lit = *(litptr++);
		  if((lit > 0) == atom[ABS(lit)]){
		      breakcount[ABS(lit)]++;
		      break;
		  }
	      }
	  }
      }
    
    numocc = numoccurence[MAXATOM+toenforce];
    occptr = occurence[MAXATOM+toenforce];
    for(i = 0; i < numocc; i++)
      {
	  /* cli = occurence[MAXATOM+toenforce][i]; */
	  cli = *(occptr++);

	  if (++numtruelit[cli] == 1){
	      numfalse--;
	      wfalse[wherefalse[cli]] =
		wfalse[numfalse];
	      wherefalse[wfalse[numfalse]] =
		wherefalse[cli];
	      /* Increment toflip's breakcount */
	      breakcount[toflip]++;

	      if (makeflag){
		/* Decrement the makecount of all vars in the clause */
		sz = size[cli];
		litptr = clause[cli];
		for (j=0; j<sz; j++){
		  /* lit = clause[cli][j]; */
		  lit = *(litptr++);
		  makecount[ABS(lit)]--;
		}
	      }
	  }
	  else if (numtruelit[cli] == 2){
	      /* Find the lit in this clause other than toflip that makes it true,
		 and decrement its breakcount */
	      sz = size[cli];
	      litptr = clause[cli];
	      for (j=0; j<sz; j++){
		  /* lit = clause[cli][j]; */
		  lit = *(litptr++);
		  if( ((lit > 0) == atom[ABS(lit)]) &&
		     (toflip != ABS(lit)) ){
		      breakcount[ABS(lit)]--;
		      break;
		  }
	      }
	  }
      }
}

int pickrandom(void)
{
    int tofix;

    tofix = wfalse[random()%numfalse];
    return Var(tofix, random()%size[tofix]);
}


int pickbest(void)
{
  int numbreak;
    int tofix;
    int clausesize;
    int i;		
    int best[MAXLENGTH];	/* best possibility so far */
    register int numbest;	/* how many are tied for best */
    register int bestvalue;	/* best value so far */
    register int var;

    tofix = wfalse[random()%numfalse];
    clausesize = size[tofix];
    numbest = 0;
    bestvalue = BIG;

    for (i=0; i< clausesize; i++){
      var = ABS(clause[tofix][i]);
      numbreak = breakcount[var];
      if (numbreak<=bestvalue){
	if (numbreak<bestvalue) numbest=0;
	bestvalue = numbreak;
	best[numbest++] = var;
      }
    }

    if (bestvalue>0 && (random()%denominator < numerator))
      return ABS(clause[tofix][random()%clausesize]);

    if (numbest == 1) return best[0];
    return best[random()%numbest];
}

int picknovelty(void)
{
  int var, diff, birthdate;
  int youngest, youngest_birthdate, best, second_best, best_diff, second_best_diff;
  int tofix, clausesize, i;

  tofix = wfalse[random()%numfalse];
  clausesize = size[tofix];  

  if (clausesize == 1) return ABS(clause[tofix][0]);

  youngest_birthdate = -1;
  best_diff = -BIG;
  second_best_diff = -BIG;

  for(i = 0; i < clausesize; i++){
    var = ABS(clause[tofix][i]);
    diff = makecount[var] - breakcount[var];
    birthdate = changed[var];
    if (birthdate > youngest_birthdate){
      youngest_birthdate = birthdate;
      youngest = var;
    }
    if (diff > best_diff || (diff == best_diff && changed[var] < changed[best])) {
      /* found new best, demote best to 2nd best */
      second_best = best;
      second_best_diff = best_diff;
      best = var;
      best_diff = diff;
    }
    else if (diff > second_best_diff || (diff == second_best_diff && changed[var] < changed[second_best])){
      /* found new second best */
      second_best = var;
      second_best_diff = diff;
    }
  }
  if (best != youngest) return best;
  if ((random()%denominator < numerator)) return second_best;
  return best;
}

int pickrnovelty(void)
{
  int var, diff, birthdate;
  int diffdiff;
  int youngest, youngest_birthdate, best, second_best, best_diff, second_best_diff;
  int tofix, clausesize, i;

  tofix = wfalse[random()%numfalse];
  clausesize = size[tofix];  

  if (clausesize == 1) return ABS(clause[tofix][0]);
  if ((numflip % 100) == 0) return ABS(clause[tofix][random()%clausesize]);

  youngest_birthdate = -1;
  best_diff = -BIG;
  second_best_diff = -BIG;

  for(i = 0; i < clausesize; i++){
    var = ABS(clause[tofix][i]);
    diff = makecount[var] - breakcount[var];
    birthdate = changed[var];
    if (birthdate > youngest_birthdate){
      youngest_birthdate = birthdate;
      youngest = var;
    }
    if (diff > best_diff || (diff == best_diff && changed[var] < changed[best])) {
      /* found new best, demote best to 2nd best */
      second_best = best;
      second_best_diff = best_diff;
      best = var;
      best_diff = diff;
    }
    else if (diff > second_best_diff || (diff == second_best_diff && changed[var] < changed[second_best])){
      /* found new second best */
      second_best = var;
      second_best_diff = diff;
    }
  }
  if (best != youngest) return best;

  diffdiff = best_diff - second_best_diff;

  if (numerator < 50 && diffdiff > 1) return best;
  if (numerator < 50 && diffdiff == 1){
    if ((random()%denominator) < 2*numerator) return second_best;
    return best;
  }
  if (diffdiff == 1) return second_best;
  if ((random()%denominator) < 2*(numerator-50)) return second_best;
  return best;
}


int picktabu(void)
{
    int numbreak[MAXLENGTH];
    int tofix;
    int clausesize;
    int i;			/* a loop counter */
    int best[MAXLENGTH];	/* best possibility so far */
    int numbest;		/* how many are tied for best */
    int bestvalue;		/* best value so far */
    int noisypick;

    tofix = wfalse[random()%numfalse];
    clausesize = size[tofix];
    for(i = 0;i < clausesize;i++)
	numbreak[i] = breakcount[ABS(clause[tofix][i])];

    numbest = 0;
    bestvalue = BIG;

    noisypick = (numerator > 0 && random()%denominator < numerator); 
    for (i=0; i < clausesize; i++) {
	if (numbreak[i] == 0) {
	    if (bestvalue > 0) {
		bestvalue = 0;
		numbest = 0;
	    }
	    best[numbest++] = i;
	}
	else if (tabu_length < numflip - changed[ABS(clause[tofix][i])]) {
	    if (noisypick && bestvalue > 0) { 
		best[numbest++] = i; 
	    }
	    else {
		if (numbreak[i] < bestvalue) {
		    bestvalue = numbreak[i];
		    numbest = 0;
		}
		if (numbreak[i] == bestvalue) {
		    best[numbest++] = i; 
		}
	    }
	}
    }
    if (numbest == 0) return NOVALUE;
    if (numbest == 1) return Var(tofix, best[0]);
    return (Var(tofix, best[random()%numbest]));
}

int countunsat(void)
	{
	int i, j, unsat, bad, lit, sign;

	unsat = 0;
	for (i=0;i < numclause;i++)
		{
		bad = TRUE;
		for (j=0; j < size[i]; j++)
			{
			lit = clause[i][j];
			sign = lit > 0 ? 1 : 0;
			if ( atom[ABS(lit)] == sign )
				{
				bad = FALSE;
				break;
				}
			}
		if (bad)
			unsat++;
		}
	return unsat;
	}

/*
#ifdef NT
double WS_elapsed_seconds(void) { return 0.0; }
#else
double WS_elapsed_seconds(void)
{
    double answer;

#ifndef WIN32
  static struct tms prog_tms;
    static struct tms prog_tms;
    static long prev_times = 0;

    (void) times(&prog_tms);

    answer = ((double)(((long)prog_tms.tms_utime)-prev_times))/((double) CLK_TCK);

    prev_times = (long) prog_tms.tms_utime;

    return answer;
}
#endif
*/

void print_sol_cnf(void)
{
    int i;
    for(i = 1;i < numatom+1;i++)
	fprintf(STDMSG, "v %i\n", solution[i] == 1 ? i : -i);
}

void
print_low_assign( int lowbad)
{
    int i;

    fprintf(STDMSG, "Begin assign with lowest # bad = %d\n", lowbad);
    for (i=1; i<=numatom; i++){
	fprintf(STDMSG, " %d", lowatom[i]==0 ? -i : i);
	if (i % 10 == 0) fprintf(STDMSG, "\n");
    }
    if ((i-1) % 10 != 0) fprintf(STDMSG, "\n");
    fprintf(STDMSG, "End assign\n");
}

void
print_current_assign(void)
{
    int i;

    fprintf(STDMSG, "Begin assign at flip = %ld\n", numflip);
    for (i=1; i<=numatom; i++){
	fprintf(STDMSG, " %d", atom[i]==0 ? -i : i);
	if (i % 10 == 0) fprintf(STDMSG, "\n");
    }
    if ((i-1) % 10 != 0) fprintf(STDMSG, "\n");
    fprintf(STDMSG, "End assign\n");
}

void
save_low_assign(void)
{
    int i;

    for (i=1; i<=numatom; i++)
      lowatom[i] = atom[i];
}

void
WS_save_solution(void)
{
    int i;

    for (i=1; i<=numatom; i++)
      solution[i] = atom[i];
}



