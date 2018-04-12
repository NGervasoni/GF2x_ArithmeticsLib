#include <stdio.h>
#include <time.h>
#include "GF2x_Arithmetics.h"

#define BILLION  1000000000L
//#define N 45
#define RANDOM_NUMBERS 100

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

void setResultArray(MPN *result) {
    for (int m = 0; m < RANDOM_NUMBERS; ++m) {
        MP_free(result[m]);
        result[m] = init_null();
    }

}

void main(int argc, char *argv[]) {

    MPN result[RANDOM_NUMBERS];

    for (int m = 0; m < RANDOM_NUMBERS; ++m) {
        result[m] = init_null();
    }
    int N = atoi(argv[1]);
//    printf("%d", N);




//    MPN irr_poly = init(irr_limb, sizeof(irr_limb) / sizeof(LIMB));

//    printf("\nPower of two = %lu\n", POWER_OF_TWO);
//    printf("\nW = %lu \tlimb_bits", LIMB_BITS);
//    printf("\nt = %lu \tmax number of limbNumber", T);
//    printf("\ns = %lu \tnumber of leftmost unused bit\n", S);
//
////    printf("\nNumber of limbs\tMP_ShiftAndAddMul\tMP_CombRtoLMul\tMP_CombLtoRMul\tMP_CombLtoRMul_w\tMP_KaratsubaMul\tMP_Toom3\tMP_Toom4");
//    printf("\nNumber of limbs\tMP_CombRtoLMul\tMP_CombLtoRMul\tMP_CombLtoRMul_w\tMP_KaratsubaMul\tMP_Toom3\tMP_Toom4");

// Calculate time taken by a request
    struct timespec requestStart, requestEnd;

//    srand(time(NULL));
    int l = N;
//    for (int l = MIN; l <= MAX; ++l) {

//        printf("\n************** %d *****************\n", l);
    printf("\n%d", l);

    LIMB limbs[l];
    MPN factors1[RANDOM_NUMBERS], factors2[RANDOM_NUMBERS];

    for (int j = 0; j < RANDOM_NUMBERS; ++j) {

        for (int i = 0; i < l; ++i) {
            limbs[i] = myRand(1, 0xffffffffffffffff);
//                                limbs[i] = myRand(1, 0xff);

        }

        factors1[j] = init(limbs, l);
    }

    for (int j = 0; j < RANDOM_NUMBERS; ++j) {

        for (int i = 0; i < l; ++i) {
            limbs[i] = myRand(1, 0xffffffffffffffff);
        }

        factors2[j] = init(limbs, l);
    }

    double accum;
    struct timespec time;
//
    //       clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    //     for (int k = 0; k < RANDOM_NUMBERS; ++k) {
//            result[k] = MP_ShiftAndAddMul(factors1[k], factors2[k], irr_poly);
//        }
//        clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
//        time = diff(requestStart, requestEnd);
//        accum = time.tv_nsec + time.tv_sec;
//        accum /= BILLION;
////        printf("\nMP_ShiftAndAddMul:\t%lf\n", accum);
//        printf("\t%lf", accum);
//        setResultArray(result);

    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < RANDOM_NUMBERS; ++k) {
        MP_CombRtoLMul(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec;
    accum /= BILLION;
//        printf("\nMP_CombRtoLMul:\t\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result);


    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < RANDOM_NUMBERS; ++k) {
        MP_CombLtoRMul(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec;
    accum /= BILLION;
//        printf("\nMP_CombLtoRMul:\t\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result);


//todo provare diverse w
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < RANDOM_NUMBERS; ++k) {
        MP_CombLtoRMul_w(&result[k], factors1[k], factors2[k], 4);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec;
    accum /= BILLION;
//        printf("\nMP_CombLtoRMul_w:\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result);

//
//
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < RANDOM_NUMBERS; ++k) {
        MP_KaratsubaMul(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec;
    accum /= BILLION;
//        printf("\nMP_KaratsubaMul:\t%lf\n", accum);
    printf("\t%lf", accum);
//
    setResultArray(result);


    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < RANDOM_NUMBERS; ++k) {

        MP_Toom3(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec;
    accum /= BILLION;
//        printf("\nMP_Toom3:\t\t\t%lf\n", accum);
    printf("\t%lf", accum);

    setResultArray(result);


    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestStart);
    for (int k = 0; k < RANDOM_NUMBERS; ++k) {
        MP_Toom4(&result[k], factors1[k], factors2[k]);
    }
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &requestEnd);
    time = diff(requestStart, requestEnd);
    accum = time.tv_nsec + time.tv_sec;
    accum /= BILLION;
//        printf("\nMP_Toom4:\t\t\t%lf\n", accum);
    printf("\t%lf", accum);

    for (int k = 0; k < RANDOM_NUMBERS; ++k) {
        MP_free(factors1[k]);
        MP_free(factors2[k]);
        MP_free(result[k]);
    }


//    }
}