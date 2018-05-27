
#ifndef GF2X_ARITHMETICSLIB_LIBRARY_H
#define GF2X_ARITHMETICSLIB_LIBRARY_H

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdbool.h>
#include <stdint-gcc.h>


//#define PRGDEBUG

#ifdef PRGDEBUG
#define PRINTF(x) printf x
#define PRINT(x) print x
#define T4(x) print x
#define T3(x) print x

#else
#define PRINTF(x) /*nothing*/
#define PRINT(x)
#define T4(x)
#define T3(x)

#endif

#define SUM_IN_FIRSTARG(a, b) { for (int i = 0; i < (b).limbNumber; i++) { \
                                    (a).num[(a).limbNumber - (b).limbNumber + i] = (a).num[(a).limbNumber - (b).limbNumber + i] ^ (b).num[i]; \
                                    }}


#define ALLOCA_EMPTY(poly, size) {  (poly).num = (LIMB *) alloca((size) * sizeof(LIMB)); \
                                    (poly).limbNumber = size; \
                                    memset((poly).num,0,(size) * sizeof(LIMB));\
                                    }

#define ALLOCA(poly, limb_pnt, size) { (poly).num = (LIMB *) alloca((size) * sizeof(LIMB)); \
                                       (poly).limbNumber = size; \
                                       memset((poly).num,0,(size) * sizeof(LIMB)); \
                                       memcpy((poly).num, limb_pnt, (size) * sizeof(LIMB)); \
}//forse memset è inutile non è la size giusta fixme

#define LEAD_ZERO_LIMB_COUNT(counter, poly){ for (int i = 0; i < (poly).limbNumber; ++i) {\
                                            if ((poly).num[i] == 0) {\
                                                (counter)++;\
                                            } else\
                                                break;\
                                           }}\

#define INIT_TO_FIT_MUL(c, a, b) {  if ((a).limbNumber > (b).limbNumber) ALLOCA_EMPTY(c, (2 * (a).limbNumber)) \
                                else ALLOCA_EMPTY(c, (2 * (b).limbNumber))};

/*---------------------------------------------------------------------------*/

// definire ogni volta il campo su cui si lavora

#define LIMB uint64_t

#define POWER_OF_TWO 12800000//100 000limb64 //5000  //m : maximum degree

#define LIMB_BITS (sizeof(LIMB) * 8) // W

#define T ((POWER_OF_TWO / LIMB_BITS) + ((POWER_OF_TWO % LIMB_BITS) != 0 ? 1 : 0)) // max number of limbs

#define S ((LIMB_BITS * T) - POWER_OF_TWO) // number of leftmost unused bit


typedef struct gf2x_mp_t {  // to be though in big-endian notation: num[0] stores the most significant bit
    LIMB *restrict num; //fixme check
    unsigned limbNumber;
} MPN;

/*---------------------------------------------------------------------------*/

MPN init_empty(unsigned size);

MPN init_null();

MPN init(LIMB A[], unsigned sizeA);

void MP_free(MPN poly);


void print(char *str, MPN poly);

void MP_bitShiftLeft(MPN *a, int bitsToShift);

void MP_bitShiftRight(MPN *a);

void limbShiftLeft(MPN *a, int n);

void removeLeadingZeroLimbs(MPN *poly);

bool isZero(MPN poly);


void MP_Addition(MPN *result, MPN a, MPN b);


void MP_ShiftAndAddMul(MPN *result, MPN factor1, MPN factor2, MPN irr_poly);

void MP_CombRtoLMul(MPN *result, MPN factor1, MPN factor2);

void MP_CombLtoRMul(MPN *result, MPN factor1, MPN factor2);

void MP_CombLtoRMul_w(MPN *res, MPN factor1, MPN factor2, unsigned w);

void MP_KaratsubaMul(MPN *result, MPN factor1, MPN factor2);

void MP_Toom3(MPN *result, MPN factor1, MPN factor2);

void MP_Toom4(MPN *result, MPN factor1, MPN factor2);

MPN MP_Squaring(MPN poly);

void MP_Reduce(MPN *result, MPN polyToreduce, MPN irr_poly);

MPN MP_Inversion_EE(MPN a, MPN irr_poly);

MPN MP_Division_Bin_Inv(MPN a, MPN b, MPN irr_poly);


void MP_exactDivOnePlusX(MPN poly);

void MP_exactDivXPlusXFour(MPN poly);

void MP_exactDivXtwoPlusXFour(MPN poly);

/*---------------------------------------------------------------------------*/

unsigned degree(MPN poly);

bool isOne(MPN poly);

bool MP_compare(MPN a, MPN b);


/*---------------------------------------------------------------------------*/

#endif