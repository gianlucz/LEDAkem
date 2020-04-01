#pragma once
#include <math.h>

static inline
uint64_t x86_64_rtdsc(void) {
  unsigned long long result;
  __asm__ volatile(".byte 15;\
                    .byte 49;\
                    shlq $32,%%rdx;\
                    orq %%rdx,%%rax" : "=a" (result) ::  "%rdx");
  return result;
}

typedef struct {
     long double mean;
     long double M2;
     long count;
} welford_t;

static inline
void welford_init(welford_t* state){
    state->mean = 0.0;
    state->M2 = 0.0;
    state->count = 0;
    return;
}

static inline
void welford_update(welford_t* state, long double sample){
    long double delta, delta2;
    state->count = state->count + 1;
    delta = sample - state->mean;
    state->mean += delta / (long double)(state->count);
    delta2 = sample - state->mean;
    state->M2 += delta * delta2;
}

static inline
void welford_print(const welford_t state){
     printf("%.2Lf, %.2Lf",
              state.mean,
              sqrtl(state.M2/(long double)(state.count-1)));
}

static inline
void welford_print_file(const welford_t state, FILE *f){

    //FILE *f = fopen("pval.txt","w");
    long double avg = state.mean;
    long double var = sqrtl(state.M2/(long double)(state.count-1));

//    fwrite(&avg, sizeof(avg),1,f);
    fprintf(f, "%.2Lf %.2Lf ", avg,var);
//    fwrite(&var, sizeof(var),1,f);

}


static inline
void welch_print(const welford_t state1, const welford_t state2, FILE *f){
    long double mean = state1.mean - state2.mean;
    long double stdev = (state1.M2/(long double)(state1.count-1))/(state1.count) +
                       (state2.M2/(long double)(state2.count-1))/(state2.count);

    /* long double df = (stdev*stdev)/(
            (pow((state1.M2/(long double)(state1.count-1)),2) + pow((state2.M2/(long double)(state2.count-1)),2))/
            ((state1.count)*(state1.count)*(long double)(state1.count-1)) //n^2(n-1)
        );
    */
    printf("  T = %.2Lf\n", mean/ sqrtl(stdev));

    // *f = fopen("pval.txt","w");
    long double t = mean/ sqrtl(stdev);
    //fwrite(&t, sizeof(t),1,f);
    fprintf(f, "%.2Lf\n", t);
}
