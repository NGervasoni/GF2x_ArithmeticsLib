#ifndef GF2X_ARITHMETICSLIB_LIBRARY_H
#define GF2X_ARITHMETICSLIB_LIBRARY_H

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdbool.h>
#include <stdint-gcc.h>

/*---------------------------------------------------------------------------*/

// definire ogni volta il campo su cui si lavora

#define LIMB uint64_t

#define POWER_OF_TWO 800 //m : maximum degree

#define LIMB_BITS (sizeof(LIMB) * 8) // W

#define T ((POWER_OF_TWO / LIMB_BITS) + ((POWER_OF_TWO % LIMB_BITS) != 0 ? 1 : 0)) // max number of limbs

#define S ((LIMB_BITS * T) - POWER_OF_TWO) // number of leftmost unused bit


typedef struct gf2x_mp_t {  // to be though in big-endian notation: num[0] stores the most significant bitsToShift ...
    LIMB *num;
    unsigned limbNumber;
} MPN;

/*---------------------------------------------------------------------------*/

MPN init_empty(unsigned size);

MPN init(LIMB A[], unsigned sizeA);

void MP_free(MPN poly);


void print(char *str, MPN poly);

void MP_bitShiftLeft(MPN *a, int bitsToShift);

void MP_bitShiftRight(MPN *a);

MPN limbShiftLeft(MPN a, int n);

MPN removeLeadingZeroLimbs(MPN poly);

bool isZero(MPN poly);


MPN MP_Addition(MPN a, MPN b);


MPN MP_ShiftAndAddMul(MPN m1, MPN m2, MPN irr_poly);

MPN MP_CombRtoLMul(MPN m1, MPN m2);

MPN MP_CombLtoRMul(MPN a, MPN b);

MPN MP_CombLtoRMul_w(MPN a, MPN b, unsigned w);

MPN MP_KaratsubaMul(MPN factor1, MPN factor2);

MPN MP_Toom3(MPN u, MPN v);

MPN MP_Toom4(MPN a, MPN b);


MPN MP_Squaring(MPN a);

MPN MP_Reduce(MPN a, MPN irr_poly, int powerOfTwo);

MPN MP_Inversion_EE(MPN a, MPN irr_poly);

MPN MP_Inversion_Binary(MPN a, MPN irr_poly);

MPN MP_Division_Bin_Inv(MPN a, MPN b, MPN irr_poly);



void MP_exactDivOnePlusX(MPN poly);

void MP_exactDivXPlusXFour(MPN poly);

void MP_exactDivXtwoPlusXFour(MPN poly);

/*---------------------------------------------------------------------------*/

unsigned degree(MPN poly);

bool isOne(MPN mp);

MPN copy(MPN poly);

bool MP_compare(MPN a, MPN b);

/*---------------------------------------------------------------------------*/

#endif