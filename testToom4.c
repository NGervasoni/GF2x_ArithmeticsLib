//
// Created by nicole on 06/05/18.
//
#include <stdio.h>
#include "GF2x_Arithmetics.h"

#define N 5
#define RANDOM_NUMBERS 1

LIMB myRand(LIMB low, LIMB high) {
    return rand() % (high - low + 1) + low;
}


void main() {
    setvbuf(stdout, 0, 2, 0);

    MPN result = init_null();

//    printf("\nPower of two = %d\n", POWER_OF_TWO);
//    printf("\nW = %lu \tlimb_bits", LIMB_BITS);
//    printf("\nt = %lu \tmax number of limbNumber", T);
//    printf("\ns = %lu \tnumber of leftmost unused bit\n", S);

//    LIMB A[N];
//    for (int i = 0; i < N; ++i) {
//        A[i] = myRand(1, 0xffffffffffffff);
//
//    }
//    LIMB B[N];
//    for (int i = 0; i < N; ++i) {
//        A[i] = myRand(1, 0xffffffffffffff);
//    }

    LIMB A[] = {0x6b8b4568, 0x327b23c7, 0x643c986a, 0x66334874, 0x74b0dc52};
    LIMB B[] = {0x19495d00, 0x2ae8944b, 0x625558ed, 0x238e1f2a, 0x46e87cce};


    unsigned sizeA = sizeof(A) / sizeof(LIMB);
    unsigned sizeB = sizeof(B) / sizeof(LIMB);

    MPN a = init(A, sizeA);
    MPN b = init(B, sizeB);

//    printf("\n************** DATA *****************\n");

//    print("\nMPN A", a);
//    print("\nMPN B", b);
//
//    MP_CombRtoLMul(&result, a, b);
//
//    print("\nresult: ", result);

//    MP_Toom4(&result, a, b);
//
//    print("\nresult: ", result);

    LIMB temp_limb[] = {0xc5d442cd93071c8, 0x16ce03898d23bbec, 0x1c3dc4bab7e52efc};
    MPN temp = init(temp_limb, 3);

    MP_bitShiftLeft(&temp, 6);
    T4(("\ntemp ", temp));
    print("\ntemp ", temp);
}

