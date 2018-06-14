#include <stdio.h>
#include <time.h>
#include <sys/resource.h>
#include "GF2x_Arithmetics.h"

#define BILLION  1000000000L

LIMB myRand(LIMB low, LIMB high) {
    return rand() % (high - low + 1) + low;
}

struct timespec diff(struct timespec start, struct timespec end) {
    struct timespec temp;

    if ((end.tv_nsec - start.tv_nsec) < 0) {
        temp.tv_sec = end.tv_sec - start.tv_sec - 1;
        temp.tv_nsec = 1000000000 + end.tv_nsec - start.tv_nsec;
    } else {
        temp.tv_sec = end.tv_sec - start.tv_sec;
        temp.tv_nsec = end.tv_nsec - start.tv_nsec;
    }
    return temp;
}

void setResultArray(MPN *result, int RANDOM_NUMBERS) {
    for (int m = 0; m < RANDOM_NUMBERS; ++m) {
        MP_free(result[m]);
        result[m] = init_null();
    }

}

bool everything_is_fine(MPN a, MPN b) {
    MPN r = init_null();
    MPN result = init_null();

    MP_CombRtoLMul(&result, a, b);
//        print("\nresult: ", result);

    // 1

    MP_CombLtoRMul_w(&r, a, b, 4);
    //print("\nr: ", r);

//    printf("\n%d)\t%d", N, MP_compare(result, r));
    if (!MP_compare(result, r))
        return false;


    MP_CombLtoRMul_w(&r, a, b, 8);
    //print("\nr: ", r);

//    printf("\t%d", MP_compare(result, r));
    if (!MP_compare(result, r))
        return false;
    // 2

    MP_KaratsubaMul(&r, a, b);
//        print("\nr: ", r);
//    printf("\t%d", MP_compare(result, r));
    if (!MP_compare(result, r))
        return false;
    // 3

    MP_Toom3(&r, a, b);
    //print("\nr: ", r);
//    printf("\t%d", MP_compare(result, r));
    if (!MP_compare(result, r))
        return false;
    // 4

    MP_Toom4(&r, a, b);
    //print("\nr: ", r);
//    printf("\t%d", MP_compare(result, r));
    if (!MP_compare(result, r))
        return false;
    // 5

    MP_CombLtoRMul(&r, a, b);
    //print("\nr: ", r);
//    printf("\t%d", MP_compare(result, r));
    if (!MP_compare(result, r))
        return false;

    return true;
}


static inline void MP_free(MPN poly) {
    free(poly.num);
} //end MP_free
void main(int argc, char *argv[]) {


    // ---------------------------- optional -----------------------------
// changing stack size to avoid stack overflow during large number multiplications

    const rlim_t stackSize = 128L * 1024L * 1024L;   // min stack size = 128 Mb
    struct rlimit rl;
    int response;

    // current stack limit

    int dim = getrlimit(RLIMIT_STACK, &rl);

    rl.rlim_cur = stackSize;
    response = setrlimit(RLIMIT_STACK, &rl);
    if (response != 0)
        printf("error when changing stack limit!\n");

    // ---------------------------- optional -----------------------------

    setvbuf(stdout, 0, 2, 0);

    int factors_size = atoi(argv[1]);
    int random_numbers = atoi(argv[2]);
    MPN result[random_numbers];

    for (int m = 0; m < random_numbers; ++m) {
        result[m] = init_null();
    }


// Calculate time taken by a request
    struct timespec requestStart, requestEnd;

//    srand(time(NULL));
    int l = factors_size;

    printf("\n%d", l);

    LIMB limbs[l];
    MPN factors1[random_numbers], factors2[random_numbers];

    for (int j = 0; j < random_numbers; ++j) {

        for (int i = 0; i < l; ++i) {
            limbs[i] = myRand(1, 0xffffffffffffff);

        }

        factors1[j] = init(limbs, l);
    }


    for (int j = 0; j < random_numbers; ++j) {

        for (int i = 0; i < l; ++i) {
            limbs[i] = myRand(1, 0xffffffffffffff);
        }

        factors2[j] = init(limbs, (unsigned) l);
    }

    double accum;
    struct timespec time;

    if (!everything_is_fine(factors1[0], factors2[0])) {
        printf("Something is not working! Aborting...\n");
        exit(EXIT_FAILURE);
    }


//1
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < random_numbers; ++k) {
        MP_CombRtoLMul(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec * BILLION;
    accum /= BILLION;
//        printf("\nMP_CombRtoLMul:\t\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result, random_numbers);

//2
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < random_numbers; ++k) {
        MP_CombLtoRMul(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec * BILLION;
    accum /= BILLION;
//        printf("\nMP_CombLtoRMul:\t\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result, random_numbers);


    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < random_numbers; ++k) {
        MP_CombLtoRMul_w(&result[k], factors1[k], factors2[k], 4);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec * BILLION;
    accum /= BILLION;
//        printf("\nMP_CombLtoRMul_w:\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result, random_numbers);


    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < random_numbers; ++k) {
        MP_CombLtoRMul_w(&result[k], factors1[k], factors2[k], 8);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec * BILLION;
    accum /= BILLION;
//        printf("\nMP_CombLtoRMul_w:\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result, random_numbers);


    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < random_numbers; ++k) {
        MP_KaratsubaMul(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec * BILLION;
    accum /= BILLION;
//        printf("\nMP_KaratsubaMul:\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result, random_numbers);

//
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < random_numbers; ++k) {

        MP_Toom3(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec * BILLION;
    accum /= BILLION;
//        printf("\nMP_Toom3:\t\t\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result, random_numbers);


    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < random_numbers; ++k) {
        MP_Toom4(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec * BILLION;
    accum /= BILLION;
//        printf("\nMP_Toom4:\t\t\t%lf\n", accum);
    printf("\t%lf", accum);

    for (int k = 0; k < random_numbers; ++k) {
        MP_free(factors1[k]);
        MP_free(factors2[k]);
        MP_free(result[k]);
    }


//    }
}