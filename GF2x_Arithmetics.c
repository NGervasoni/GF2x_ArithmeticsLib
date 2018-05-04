
#include <assert.h>
#include "GF2x_Arithmetics.h"

uint16_t precomputed[256];

bool init_precomputed = 0;

void create_precomputed() {
    for (unsigned j = 0; j < 256; ++j) {

        uint8_t temp = (uint8_t) j;
        precomputed[j] = (uint16_t) (0 + (temp & 0x1));

        for (unsigned i = 1; i < 8; ++i) {
            temp = temp >> 1;
            precomputed[j] = (uint16_t) (precomputed[j] + (temp & 1) * pow(2, 2 * i));

        }
    }
    init_precomputed = 1;
} // end create_precomputed
/*---------------------------------------------------------------------------*/
//Checks if the polynomial belongs to the defined ring
bool properSize(MPN poly) {
    if (poly.limbNumber < T)
        return true;
    if (poly.limbNumber > T)
        return false;
    //poly.limbNumber is T
    for (int i = LIMB_BITS - 1; i >= LIMB_BITS - S; i--) {
        if (poly.num[0] >> i == 1)
            return false;
    }
    return true;
}

/*---------------------------------------------------------------------------*/

MPN init_empty(unsigned size) {
    MPN res;
    res.num = (LIMB *) calloc(size, sizeof(LIMB));
    res.limbNumber = size;
    return res;
} // end init_empty

/*---------------------------------------------------------------------------*/

MPN init_null() {
    MPN res;
    res.num = NULL;
    res.limbNumber = 0;
    return res;
}
// end init_empty

/*---------------------------------------------------------------------------*/

MPN init(LIMB A[], unsigned sizeA) {
    MPN res = init_empty(sizeA);
    memcpy(res.num, A, sizeA * sizeof(LIMB));
    return res;
} // end init

/*---------------------------------------------------------------------------*/

void MP_free(MPN poly) {
    free(poly.num);
} //end MP_free

/*---------------------------------------------------------------------------*/
// 2.32
//a, b are polynomial of degree <= POWER_OF_TWO, *res points to an INITIALIZED MPN where the c will be stored

void MP_Addition(MPN *result, MPN a, MPN b) {

    if (!properSize(a) || !properSize(b)) {
        fprintf(stderr, "Wrong polynomial dimension! Aborting...\n");
        exit(EXIT_FAILURE);
    }

    unsigned maxLength, minLength;
    LIMB *ptrMax, *ptrMin;
    if (a.limbNumber > b.limbNumber) {
        maxLength = a.limbNumber;
        minLength = b.limbNumber;
        ptrMax = a.num;
        ptrMin = b.num;
    } else {
        maxLength = b.limbNumber;
        minLength = a.limbNumber;
        ptrMax = b.num;
        ptrMin = a.num;
    }
    MPN c = init_empty(maxLength);

    for (int i = 0; i < minLength; i++) {
        c.num[maxLength - minLength + i] = ptrMax[maxLength - minLength + i] ^ ptrMin[i];
    }
    for (int i = 0; i < maxLength - minLength; i++) {
        c.num[i] = ptrMax[i];
    }
    MP_free(*result);
    *result = c;

}// end MP_addition

/*---------------------------------------------------------------------------*/

inline void MP_bitShiftLeft(MPN *a, const int bitsToShift) {


    if (bitsToShift == 0) {
        return;
    }

    if (a->limbNumber == 0) return;

    assert(bitsToShift < LIMB_BITS);

    if (a->num[0] >> LIMB_BITS - 1) { // checks if first limb bit is 1

        MPN c = init_empty(a->limbNumber + 1);
        MP_Addition(a, *a, c);

        MP_free(c);
    }


    int j;
    LIMB mask;
    mask = ~(((LIMB) 0x01 << (LIMB_BITS - bitsToShift)) - 1);

    for (j = 0; j < a->limbNumber - 1; j++) {
        a->num[j] <<= bitsToShift;
        a->num[j] |= (a->num[j + 1] & mask) >> (LIMB_BITS - bitsToShift);
    }
    a->num[j] <<= bitsToShift;
}


/*---------------------------------------------------------------------------*/

void MP_bitShiftRight(MPN *a) {

    LIMB shifted_bit = 1;
    shifted_bit = shifted_bit << (LIMB_BITS - 1);
    uint8_t curr_last_bit = 0;
    uint8_t prev_last_bit = 0;

    for (unsigned i = 0; i < a->limbNumber; ++i) {

        if (a->num[i] & 1)
            curr_last_bit = 1;
        else curr_last_bit = 0;

        a->num[i] = (a->num[i] >> 1);

        if (prev_last_bit)
            a->num[i] ^= shifted_bit;

        prev_last_bit = curr_last_bit;

    }

}// end MP_bitShiftRight

/*---------------------------------------------------------------------------*/

void limbShiftLeft(MPN *a, int n) {

    MPN c = init_empty(a->limbNumber + n);

    for (unsigned i = 0; i < a->limbNumber; i++) {
        c.num[i] = a->num[i];
    }

    MP_free(*a);
    *a = c;


} // end limbShiftLeft

/*---------------------------------------------------------------------------*/
//2.33
// assumption: m1, m2 are polynomial of degree <= POWER_OF_TWO, irreducible is an
// irreducible polynomial of degree POWER_OF_TWO+1

void MP_ShiftAndAddMul(MPN *result, MPN factor1, MPN factor2, MPN irr_poly) {

    if (irr_poly.limbNumber > T + 1) {
        fprintf(stderr, "Irr poly is too big! Aborting...\n");
        exit(EXIT_FAILURE);
    }

    MPN a = init_empty(T), b = init_empty(T), c;


    MP_Addition(&a, factor1, a);
    MP_Addition(&b, factor2, b);


    unsigned shiftToHigherOne = (LIMB_BITS - S);

    // trovo valore da controllare poi su b
    // (sarebbe la posizione che sfora di uno il grado e a cui addiziono il polinomio irr

    for (int i = (int) (irr_poly.limbNumber - 1); i >= 0; --i) {

        for (unsigned j = 0; j < LIMB_BITS; ++j) {

// initial setting of c
            if (i == (int) (irr_poly.limbNumber - 1) && j == 0) {
                if (a.num[a.limbNumber - 1] & 0x1) {
                    c = init(b.num, irr_poly.limbNumber);
                } else {
                    c = init_empty(irr_poly.limbNumber);
                }

            } else {

                MP_bitShiftLeft(&b, 1);
                if (b.num[0] >> shiftToHigherOne) {
                    MP_Addition(&b, b, irr_poly);
                }
                if ((a.num[i] >> j) & 0x1)
                    MP_Addition(&c, c, b);
            }

        }
    }

    MP_free(a);
    MP_free(b);
    MP_free(*result);
    *result = c;

}// end MP_ShiftAndAddMul

/*---------------------------------------------------------------------------*/

//2.34
//ASSUMPTION: m1, m2 limbNumb max is T
void MP_CombRtoLMul(MPN *result, MPN factor1, MPN factor2) {

    MPN b = init_null(), c;
    MP_Addition(&b, factor2, init_empty(factor2.limbNumber + 1));
    c = init_empty(2 * T);

    // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
    for (int k = 0; k < LIMB_BITS; ++k) {
        // j seleziona a ogni ciclo il limb
        for (int j = factor1.limbNumber - 1; j >= 0; --j) {
            // shift di k posizioni (k=0 => seleziono bit più a destra)
            if (factor1.num[j] >> k & 0x1) { //OKKK!!

                for (int i = 0; i < b.limbNumber; ++i) {
                    c.num[c.limbNumber - 1 - (factor1.limbNumber - 1 - j) - i] ^= b.num[b.limbNumber - 1 - i];
                }
            }
        }
        if (k != LIMB_BITS - 1)
            MP_bitShiftLeft(&b, 1);
    }

    MP_free(b);
    removeLeadingZeroLimbs(&c);
    MP_free(*result);
    *result = c;

} // end MP_CombRtoLMul


/*---------------------------------------------------------------------------*/
//2.35
//ASSUMPTION: a, b limbNumb max is T
void MP_CombLtoRMul(MPN *result, MPN factor1, MPN factor2) {

    MPN c;
    c = init_empty(2 * T);

    // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
    for (int k = LIMB_BITS - 1; k >= 0; --k) {

        // j seleziona a ogni ciclo il limb
        for (int j = factor1.limbNumber - 1; j >= 0; --j) {

            // shift di k posizioni (k=0 => seleziono bit più a destra)
            if (factor1.num[j] >> k & 0x1) {

                for (int i = 0; i < factor2.limbNumber; ++i) {

                    c.num[c.limbNumber - 1 - (factor1.limbNumber - 1 - j) - i] ^= factor2.num[factor2.limbNumber - 1 -
                                                                                              i];

                }
            }
        }
        if (k != 0)
            MP_bitShiftLeft(&c, 1);
    }
    MP_free(*result);
    *result = c;

} // end MP_CombLtoRMul

/*---------------------------------------------------------------------------*/
//2.36

//ASSUMPTION: a, b limbNumb max is T
//            w divisore di LIMB_BITS
void MP_CombLtoRMul_w(MPN *res, MPN factor1, MPN b, unsigned w) {

    MPN c;

    c = init_empty(2 * T);

    int b_u_array_size = (int) pow(2, w);
    LIMB b_u_index = 0;
    MPN b_u[b_u_array_size];

    b_u[0] = init(&b_u_index, 1);
    for (int l = 1; l < b_u_array_size; ++l) {

        b_u_index = (LIMB) l;

        b_u[l] = init_null();
        MP_CombLtoRMul(&b_u[l], b, init(&b_u_index, 1));
        removeLeadingZeroLimbs(&b_u[l]);
    }

    // k rappresenta il numero di shift in un limb
    for (int k = (LIMB_BITS / w) - 1; k >= 0; --k) {
        // j seleziona a ogni ciclo il limb
        for (int j = factor1.limbNumber - 1; j >= 0; --j) {


            LIMB w_bits_value = ((factor1.num[j] >> (k * w)) & ((LIMB) pow(2, w) - 1));

            MPN bu = b_u[w_bits_value];

            for (int i = 0; i < bu.limbNumber; ++i) {
                c.num[c.limbNumber - 1 - (factor1.limbNumber - 1 - j) - i] ^= bu.num[bu.limbNumber - 1 - i];
            }


        }
        if (k != 0)
            MP_bitShiftLeft(&c, w);


    }
    MP_free(*res);
    *res = c;


} // end MP_CombLtoRMul_w


/*---------------------------------------------------------------------------*/

void MP_KaratsubaMul(MPN *result, MPN factor1, MPN factor2) {

    if (factor1.limbNumber == 1 && factor2.limbNumber == 1) {
        MP_CombRtoLMul(result, factor1, factor2);
        return;
    }

    MPN a = init(factor1.num, factor1.limbNumber), b = init(factor2.num, factor2.limbNumber);
    MPN zero = init_empty(1);

    if (a.limbNumber > b.limbNumber) {
        MP_Addition(&b, init_empty(a.limbNumber), b);
    } else if (b.limbNumber > a.limbNumber) {
        MP_Addition(&a, init_empty(b.limbNumber), a);
    }


    if (a.limbNumber != 1 && b.limbNumber != 1) {

        MPN first = init_null(), second = init_null(), third = init_null(), A_01 = init_null(), B_01 = init_null(), a01perb01 = init_null();

        MPN c;

        MPN A_0 = init(&a.num[0], a.limbNumber - (a.limbNumber) / 2);
        MPN A_1 = init(&a.num[a.limbNumber - (a.limbNumber) / 2], (a.limbNumber) / 2);

        MPN B_0 = init(&b.num[0], b.limbNumber - (b.limbNumber) / 2);
        MPN B_1 = init(&b.num[b.limbNumber - (b.limbNumber) / 2], (b.limbNumber) / 2);

        if (isZero(A_0) || isZero(B_0))
            first = zero;
        else
            MP_KaratsubaMul(&first, A_0, B_0);

        c = init(first.num, first.limbNumber);
        limbShiftLeft(&c, b.limbNumber - b.limbNumber % 2);

        MP_KaratsubaMul(&third, A_1, B_1);
        MP_Addition(&c, c, third);

        MP_Addition(&A_01, A_0, A_1);

        MP_Addition(&B_01, B_0, B_1);

        MP_Addition(&second, first, third);
        MP_KaratsubaMul(&a01perb01, A_01, B_01);
        MP_Addition(&second, second, a01perb01);

        limbShiftLeft(&second, (b.limbNumber) / 2);


        MP_Addition(&c, c, second);

        MP_free(first);
        MP_free(second);
        MP_free(third);
        MP_free(A_01);
        MP_free(B_01);
        MP_free(a01perb01);
        MP_free(a);
        MP_free(b);
        MP_free(*result);
        *result = c;
        return;
    }


    MPN *ptrLenIsOne, *ptrOther;
    if (factor1.limbNumber == 1) {
        ptrLenIsOne = &factor1;
        ptrOther = &factor2;
    } else if (factor2.limbNumber == 1) {
        ptrLenIsOne = &factor2;
        ptrOther = &factor1;
    }

    MPN c;

    MPN A_0 = init(&(ptrLenIsOne->num[0]), 1);

    MPN B_0 = init(&(ptrOther->num[0]), ptrOther->limbNumber - (ptrOther->limbNumber) / 2);
    MPN B_1 = init(&(ptrOther->num[ptrOther->limbNumber - (ptrOther->limbNumber) / 2]), (ptrOther->limbNumber) / 2);

    MPN A0B0 = init_null();
    MP_KaratsubaMul(&A0B0, A_0, B_0);
    MPN A0B1 = init_null();
    MP_KaratsubaMul(&A0B1, A_0, B_1);

    c = init(A0B0.num, A0B0.limbNumber);

    limbShiftLeft(&c, ptrOther->limbNumber);

    MP_Addition(&c, c, A0B1);

    MP_free(zero);
    MP_free(A_0);
    MP_free(B_0);
    MP_free(B_1);
    MP_free(A0B0);
    MP_free(A0B1);

    MP_free(*result);
    *result = c;


} //end MP_KaratsubaMul

/*---------------------------------------------------------------------------*/
//2.39
MPN MP_Squaring(MPN poly) {

    if (!init_precomputed) {
        create_precomputed();
    }

    MPN c = init_empty(2 * poly.limbNumber);

    int n = poly.limbNumber;
    int n1 = sizeof(poly.num[0]);
    uint8_t *a1 = (uint8_t *) poly.num;
    uint16_t *c1 = (uint16_t *) c.num;
    int k = 0;

    if (n1 == 1) {
        for (int i = 0; i < n; i++) {
            c1[i] = (precomputed[a1[i]] << 8) ^ (precomputed[a1[i]] >> 8);
        }
        return c;
    }

    int h = n1 / 2 - 1;

    for (int i = 0; i < n; i++) {
        for (int j = n1 - 1; j >= 0; j--) {

            c1[(k * n1) + h] = precomputed[a1[j + (i * n1)]];

            h--;
            if (h == -1) {
                h = n1 - 1;
            }
        }
        k++;
    }
    return c;
} // end MP_Squaring

/*---------------------------------------------------------------------------*/
//2.40
// assumption: a has degree <= 2m-2, irr proper
// irr(z) = z^m + r(z) where degree of r(z) is <= m-1

void MP_Reduce(MPN *result, MPN polyToreduce, MPN irr_poly) {

    int block, tot_bits, extra_bits, extra_block;

    MPN c, r = init(irr_poly.num, irr_poly.limbNumber);
    MPN u[LIMB_BITS] = {0};

    int limb = 0, temp = 0;
    for (int j = 0; j < r.limbNumber && temp == 0; ++j) {
        for (int i = LIMB_BITS - 1; i >= 0; i--) {

            if (r.num[j] >> i & 1) {
                temp = i; //posizione bit da levare è limbnumber-temp
                limb = j;  //limb da cui levare il primo 1
                break;
            }
        }
    }

    r.num[limb] = r.num[limb] ^ (LIMB) pow(2, temp);

// Precomputation of z^k * r(z)
    for (int k = 0; k < LIMB_BITS; ++k) {
        u[k] = init(r.num, r.limbNumber);
        MP_bitShiftLeft(&r, 1);
    }

    tot_bits = (LIMB_BITS * polyToreduce.limbNumber); //number of bitsToShift in polyToreduce

    for (int l = tot_bits - 1; l >= POWER_OF_TWO; l--) {

        block = (tot_bits - 1 - l) / LIMB_BITS;

        if (polyToreduce.num[block] >> (LIMB_BITS * (1 + block) - 1 - (tot_bits - 1 - l)) & 1) {

            int j = (l - POWER_OF_TWO) / LIMB_BITS;
            int k = (l - POWER_OF_TWO) - LIMB_BITS * j;

            MPN u_k = u[k];

            for (int i = 0; i < u_k.limbNumber; ++i) {
                polyToreduce.num[polyToreduce.limbNumber - 1 - j - i] ^= u_k.num[u_k.limbNumber - 1 - i];
            }
        }
    }

    c = init_empty(T);

    LIMB mask = (LIMB) ~(((1 << S) - 1) << (LIMB_BITS - S));

    for (int m = T - 1; m >= 0; m--) {
        if (m == 0) {
            c.num[0] = polyToreduce.num[polyToreduce.limbNumber - 1 - (T - 1 - m)] & mask;
        } else
            c.num[m] = polyToreduce.num[polyToreduce.limbNumber - 1 - (T - 1 - m)];

    }

    MP_free(r);
    for (int k = 0; k < LIMB_BITS; ++k) {
        MP_free(u[k]);
    }

    removeLeadingZeroLimbs(&c);
    MP_free(*result);
    *result = c;

} //end MP_Reduce

/*---------------------------------------------------------------------------*/
//2.48
//Assumptions a has max degree m-1, irr_poly is an irreducible polynomial with degree m
//Inversion using extended euclidian algorithm
MPN MP_Inversion_EE(MPN a, MPN irr_poly) {

    MPN swap, shifted_v, shifted_g2;
    MPN u = init(a.num, a.limbNumber);
    MPN v = init(irr_poly.num, irr_poly.limbNumber);

    LIMB one[] = {1};
    LIMB zero[] = {0};

    MPN g1 = init(one, 1);
    MPN g2 = init(zero, 1);


    while (!(isOne(u))) {

        int j = degree(u) - degree(v);

        if (j < 0) { //swap u,v g1,g2

            swap = u;
            u = v;
            v = swap;

            swap = g1;
            g1 = g2;
            g2 = swap;

            j = -j;
        }

        shifted_v = init(v.num, v.limbNumber);
        shifted_g2 = init(g2.num, g2.limbNumber);

        for (int l = 0; l < j; ++l) {
            MP_bitShiftLeft(&shifted_v, 1);
            MP_bitShiftLeft(&shifted_g2, 1);
        }

        MP_Addition(&u, u, shifted_v);
        MP_Addition(&g1, g1, shifted_g2);

        MP_free(shifted_g2);
        MP_free(shifted_v);
    }

    MP_free(u);
    MP_free(v);
    MP_free(g2);
    return g1;
}
/*    ------------------------------------------------------------------------*/

/*
 * Assumptions: a!=0, b have max degree m-1 , irr_poly is an irreducible polynomial with degree m
 * It exploits binary inversion algorithm.
 * Return c = b/a = b*a^-1
 */

MPN MP_Division_Bin_Inv(MPN a, MPN b, MPN irr_poly) {

    if (isZero(b)) {
        fprintf(stderr, "Division by zero! Aborting...\n");
        exit(EXIT_FAILURE);
    }

    MPN u = init(b.num, b.limbNumber);
    MPN v = init(irr_poly.num, irr_poly.limbNumber);

    LIMB zero[] = {0};

    MPN g1 = init(a.num, a.limbNumber);
    MPN g2 = init(zero, 1);

    while (!isOne(u) && !isOne(v)) {

        while (!isZero(u) && (u.num[u.limbNumber - 1] & 1) == 0) { //z divides u

            MP_bitShiftRight(&u); // u = u/z

            if ((g1.num[g1.limbNumber - 1] & 1)) { //z doesn't divide g1
                MP_Addition(&g1, irr_poly, g1);
            }

            MP_bitShiftRight(&g1);
        }

        while (!isZero(v) && (v.num[v.limbNumber - 1] & 1) == 0) {

            MP_bitShiftRight(&v); // v = v/z

            if ((g2.num[g2.limbNumber - 1] & 1)) { //z doesn't divide g1
                MP_Addition(&g2, irr_poly, g2);
            }

            MP_bitShiftRight(&g2);
        }

        if (degree(u) > degree(v)) {
            MP_Addition(&u, v, u);
            MP_Addition(&g1, g2, g1);

        } else {
            MP_Addition(&v, u, v);
            MP_Addition(&g2, g1, g2);
        }
    }

    if (isOne(u)) {
        MP_free(u);
        MP_free(v);
        MP_free(g2);
        removeLeadingZeroLimbs(&g1);
        return g1;
    } else {
        MP_free(u);
        MP_free(v);
        MP_free(g1);
        removeLeadingZeroLimbs(&g2);
        return g2;
    }

} // end MP_Division_Bin_Inv


/*---------------------------------------------------------------------------*/

void MP_exactDivOnePlusX(MPN poly) {
    LIMB t = 0;
    long i;

    for (i = poly.limbNumber - 1; i >= 0; i--) {
        t ^= poly.num[i];

        for (int j = 1; j <= LIMB_BITS / 2; j = j * 2) {
            t ^= t << j;
        }
        poly.num[i] = t;
        t >>= LIMB_BITS - 1;
    }
} // end MP_exactDivOnePlusX


/*---------------------------------------------------------------------------*/
void MP_exactDivXPlusXFour(MPN c) {

    LIMB t = 0;
    long i;
    unsigned shift;

    MPN reverse = init_empty(c.limbNumber);

    for (int j = 0, k = c.limbNumber - 1; j < c.limbNumber; k--, ++j) {
        reverse.num[j] = c.num[k];
    }

    for (i = 0; i < reverse.limbNumber; i++) {
        t ^= (reverse.num[i] >> 1) | ((i + 1 < reverse.limbNumber) ? (reverse.num[i + 1] << (LIMB_BITS - 1)) : 0);
        shift = 3;
        while (LIMB_BITS >= shift) {
            t ^= t << shift ^ ((shift * 2 > LIMB_BITS) ? 0 : (t << shift * 2));
            shift = shift * 3;
        }
        reverse.num[i] = t;
        t >>= (LIMB_BITS - 3);
    }

    for (int j = 0, k = c.limbNumber - 1; j < c.limbNumber; k--, ++j) {
        c.num[j] = reverse.num[k];
    }

} // end MP_exactDivXPlusXFour


/*---------------------------------------------------------------------------*/

void MP_exactDivXtwoPlusXFour(MPN poly) {

    LIMB cy = 0, t;
    long i;

    MPN reverse = init_empty(poly.limbNumber);

    for (int j = 0, k = poly.limbNumber - 1; j < poly.limbNumber; k--, ++j) {
        reverse.num[j] = poly.num[k];
    }

    for (i = reverse.limbNumber - 1; i >= 0; i--) {
        t = (reverse.num[i] >> 2) | (cy << (LIMB_BITS - 2));
        cy = reverse.num[i] & 3UL;
        reverse.num[i] = t;
    }

    t = 0;

    for (i = 0; i < reverse.limbNumber; i++) {
        t ^= reverse.num[i];
        for (int j = 2; j <= LIMB_BITS / 2; j = j * 2) {
            t ^= t << j;
        }
        reverse.num[i] = t;
        t >>= (LIMB_BITS - 2);
    }

    for (int j = 0, k = poly.limbNumber - 1; j < poly.limbNumber; k--, ++j) {
        poly.num[j] = reverse.num[k];
    }

} //end MP_exactDivXtwoPlusXFour

/*---------------------------------------------------------------------------*/

void MP_Toom3(MPN *result, MPN factor1, MPN factor2) {

    MPN u = init(factor1.num, factor1.limbNumber), v = init(factor2.num, factor2.limbNumber);


    if (u.limbNumber < 3 && v.limbNumber < 3) {
        MP_CombRtoLMul(result, u, v);
        return;
    }


    MPN u2, u1, u0, v2, v1, v0;
    MPN *ptrMax, *ptrMin;


    if (u.limbNumber >= v.limbNumber) {
        ptrMax = &u;
        ptrMin = &v;
    } else {
        ptrMax = &v;
        ptrMin = &u;
    }

    MP_Addition(ptrMin, init_empty(ptrMax->limbNumber), *ptrMin);


    unsigned u_limbs_div3 = u.limbNumber / 3;
    int bih;
//limbNumber multiplo di 3
    if (u_limbs_div3 * 3 == u.limbNumber) {
        u2 = init(&(u.num[0]), u_limbs_div3);
        u1 = init(&(u.num[u_limbs_div3]), u_limbs_div3);
        u0 = init(&(u.num[2 * u_limbs_div3]), u_limbs_div3);

        v2 = init(&(v.num[0]), u_limbs_div3);
        v1 = init(&(v.num[u_limbs_div3]), u_limbs_div3);
        v0 = init(&(v.num[2 * u_limbs_div3]), u_limbs_div3);

        bih = u_limbs_div3;


    } else {

        unsigned blocks = 2 + 2 * u_limbs_div3;

        u2 = init(&(u.num[0]), u.limbNumber - blocks);
        u1 = init(&(u.num[u.limbNumber - blocks]), u_limbs_div3 + 1);
        u0 = init(&(u.num[u.limbNumber - u_limbs_div3 - 1]), u_limbs_div3 + 1);


        v2 = init(&(v.num[0]), v.limbNumber - blocks);
        v1 = init(&(v.num[v.limbNumber - blocks]), u_limbs_div3 + 1);
        v0 = init(&(v.num[v.limbNumber - u_limbs_div3 - 1]), u_limbs_div3 + 1);
        bih = u_limbs_div3 + 1;

    }


    MPN w = init_null();
    MPN w0 = init_null(), w1 = init_null(), w2 = init_null(), w3 = init_null(), w4 = init_null();

    LIMB xterzapiuuno_limb[] = {0x9};
    MPN xterzapiuuno = init(xterzapiuuno_limb, 1);


    //EVALUATION

    MPN temp = init_null();
    MP_Addition(&temp, u0, u1);
    MP_Addition(&w3, temp, u2);

    MP_Addition(&temp, v0, v1);
    MP_Addition(&w2, temp, v2);

    MP_Toom3(&w1, w3, w2);

    MPN u2perx2 = init(u2.num, u2.limbNumber);
    MP_bitShiftLeft(&u2perx2, 2);

    MPN u1perx = init(u1.num, u1.limbNumber);
    MP_bitShiftLeft(&u1perx, 1);

    MP_Addition(&w0, u2perx2, u1perx);

    MPN v2perx2 = init(v2.num, v2.limbNumber);
    MP_bitShiftLeft(&v2perx2, 2);

    MPN v1perx = init(v1.num, v1.limbNumber);
    MP_bitShiftLeft(&v1perx, 1);

    MP_Addition(&w4, v2perx2, v1perx);

    MP_Addition(&w3, w3, w0);
    MP_Addition(&w2, w2, w4);

    MP_Addition(&w0, w0, u0);
    MP_Addition(&w4, w4, v0);

    MP_Toom3(&w3, w3, w2);
    MP_Toom3(&w2, w0, w4);


    MP_Toom3(&w4, u2, v2);
    MP_Toom3(&w0, u0, v0);


    //INTERPOLATION


    MP_Addition(&w3, w3, w2);


    MP_Addition(&w2, w2, w0);

    MP_bitShiftRight(&w2);

    MP_Addition(&temp, w2, w3);
    MP_Toom3(&xterzapiuuno, xterzapiuuno, w4);
    MP_Addition(&w2, temp, xterzapiuuno);


    MP_exactDivOnePlusX(w2);


    MP_Addition(&w1, w1, w0);


    MP_Addition(&w3, w3, w1);

    MP_bitShiftRight(&w3);

    MP_exactDivOnePlusX(w3);


    MP_Addition(&temp, w1, w4);
    MP_Addition(&w1, temp, w2);


    MP_Addition(&w2, w2, w3);


    limbShiftLeft(&w1, 1 * bih);
    MP_Addition(&w, w0, w1);
    limbShiftLeft(&w2, 2 * bih);
    MP_Addition(&w, w, w2);
    limbShiftLeft(&w3, 3 * bih);
    MP_Addition(&w, w, w3);
    limbShiftLeft(&w4, 4 * bih);
    MP_Addition(&w, w, w4);

    MP_free(temp);
    MP_free(u);
    MP_free(u0);
    MP_free(u1);
    MP_free(u1perx);
    MP_free(u2);
    MP_free(u2perx2);
    MP_free(v);
    MP_free(v0);
    MP_free(v1);
    MP_free(v1perx);
    MP_free(v2);
    MP_free(v2perx2);
    MP_free(xterzapiuuno);
    MP_free(w0);
    MP_free(w1);
    MP_free(w2);
    MP_free(w3);
    MP_free(w4);
    MP_free(*result);
    removeLeadingZeroLimbs(&w);
    *result = w;
} // end MP_Toom3


/*---------------------------------------------------------------------------*/

void MP_Toom4(MPN *result, MPN factor1, MPN factor2) {

    if (factor1.limbNumber < 4 && factor2.limbNumber < 4) {
        MP_CombRtoLMul(result, factor1, factor2);
        return;
    }


    MPN u = init(factor1.num, factor1.limbNumber);
    MPN v = init(factor2.num, factor2.limbNumber);


    MPN u3, u2, u1, u0, v3, v2, v1, v0, w = init_null(), w0 = init_null(), w1 = init_null(),
            w2 = init_null(), w3 = init_null(), w4 = init_null(), w5 = init_null(), w6 = init_null();
    MPN *ptrMax, *ptrMin;
    unsigned u_limbs_div4;
    int bih;

    LIMB xpiuuno_limb[] = {0x3};
    MPN xpiuuno = init(xpiuuno_limb, 1);

    if (u.limbNumber >= v.limbNumber) {
        ptrMax = &u;
        ptrMin = &v;
    } else {
        ptrMax = &v;
        ptrMin = &u;
    }

    MP_Addition(ptrMin, init_empty(ptrMax->limbNumber), *ptrMin);


    u_limbs_div4 = u.limbNumber / 4;


    if (u_limbs_div4 * 4 == u.limbNumber) {

        u3 = init(&(u.num[0]), u_limbs_div4);
        u2 = init(&(u.num[u_limbs_div4]), u_limbs_div4);
        u1 = init(&(u.num[2 * u_limbs_div4]), u_limbs_div4);
        u0 = init(&(u.num[3 * u_limbs_div4]), u_limbs_div4);

        v3 = init(&(v.num[0]), u_limbs_div4);
        v2 = init(&(v.num[u_limbs_div4]), u_limbs_div4);
        v1 = init(&(v.num[2 * u_limbs_div4]), u_limbs_div4);
        v0 = init(&(v.num[3 * u_limbs_div4]), u_limbs_div4);

        bih = u_limbs_div4;

    } else {

        unsigned remaining_limbs = u.limbNumber;
        unsigned blocks = u_limbs_div4 + 1;;

        u0 = init(&(u.num[u.limbNumber - u_limbs_div4 - 1]), blocks);
        v0 = init(&(v.num[v.limbNumber - u_limbs_div4 - 1]), blocks);

        u1 = init(&(u.num[u.limbNumber - 2 * blocks]), blocks);
        v1 = init(&(v.num[v.limbNumber - 2 * blocks]), blocks);

        remaining_limbs -= 2 * blocks;

        if (remaining_limbs >= blocks) {
            u2 = init(&(u.num[u.limbNumber - 3 * blocks]), blocks);
            v2 = init(&(v.num[v.limbNumber - 3 * blocks]), blocks);

            remaining_limbs -= blocks;
            if (remaining_limbs > 0) {
                u3 = init(&(u.num[0]), remaining_limbs);
                v3 = init(&(v.num[0]), remaining_limbs);
            } else {
                u3 = init_empty(1);
                v3 = init_empty(1);
            }
        } else if (remaining_limbs > 0) {
            u2 = init(&(u.num[0]), remaining_limbs);
            u3 = init_empty(1);

            v2 = init(&(v.num[0]), remaining_limbs);
            v3 = init_empty(1);
        } else {
            u2 = init_empty(1);
            u3 = init_empty(1);

            v2 = init_empty(1);
            v3 = init_empty(1);
        }


        bih = u_limbs_div4 + 1;

    }


    //EVALUATION
    MP_Addition(&w1, u1, u0);
    MP_Addition(&w1, u2, w1);
    MP_Addition(&w1, u3, w1);

    MP_Addition(&w2, v1, v0);
    MP_Addition(&w2, v2, w2);
    MP_Addition(&w2, v3, w2);

    MP_Toom4(&w3, w1, w2);

    MPN temp = init(u3.num, u3.limbNumber); //per 0x2
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&temp, u2, temp);
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w0, u1, temp);

    MP_free(temp);
    temp = init(v3.num, v3.limbNumber); //per 0x2
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&temp, v2, temp);
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w6, v1, temp);

    MP_Toom4(&temp, u3, xpiuuno);
    MP_Addition(&temp, w0, temp);
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w4, w1, temp);

    MP_Toom4(&temp, v3, xpiuuno);
    MP_Addition(&temp, w6, temp);
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w5, temp, w2);

    MP_bitShiftLeft(&w0, 1);
    MP_Addition(&w0, u0, w0);

    MP_bitShiftLeft(&w6, 1);
    MP_Addition(&w6, v0, w6);

    MP_Toom4(&w5, w5, w4);
    MP_Toom4(&w4, w6, w0);

    MP_free(temp);
    temp = init(u2.num, u2.limbNumber);
    MP_bitShiftLeft(&temp, 1);
    MPN temp1;
    temp1 = init(u1.num, u1.limbNumber);
    MP_bitShiftLeft(&temp1, 2);
    MP_Addition(&w0, temp, temp1);
    MP_free(temp);
    temp = init(u0.num, u0.limbNumber);
    MP_bitShiftLeft(&temp, 3); //per x^3
    MP_Addition(&w0, temp, w0);

    MP_free(temp);
    temp = init(v2.num, v2.limbNumber);
    MP_bitShiftLeft(&temp, 1);
    temp1 = init(v1.num, v1.limbNumber);
    MP_bitShiftLeft(&temp1, 2);
    MP_Addition(&w6, temp, temp1);
    MP_free(temp);
    temp = init(v0.num, v0.limbNumber);
    MP_bitShiftLeft(&temp, 3); //per x^3
    MP_Addition(&w6, temp, w6);

    MP_Addition(&w1, w0, w1);

    MP_free(temp);
    temp = init(u0.num, u0.limbNumber);
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w1, temp, w1); // w1 + u0*x
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w1, w1, temp); // w1 + u0*x^2

    MP_Addition(&w2, w6, w2);
    MP_free(temp);
    temp = init(v0.num, v0.limbNumber);
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w2, temp, w2); // w2 + u0*x
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w2, temp, w2); // w2 + u0*x^2

    MP_Addition(&w0, u3, w0);

    MP_Addition(&w6, v3, w6);

    MP_Toom4(&w1, w1, w2);

    MP_Toom4(&w2, w0, w6);

    MP_Toom4(&w6, u3, v3);

    MP_Toom4(&w0, u0, v0);


    //INTERPOLATION

    MP_Addition(&w1, w2, w1);
    MP_Addition(&w1, w0, w1); //+w0
    MP_free(temp);
    temp = init(w0.num, w0.limbNumber);
    MP_bitShiftLeft(&temp, 2); //+w0*x^2
    MP_Addition(&w1, temp, w1);
    MP_bitShiftLeft(&temp, 2);
    MP_Addition(&w1, temp, w1); //+w0*x^4

    MP_Addition(&w5, w4, w5);
    MP_Addition(&w5, w6, w5);
    MP_free(temp);
    temp = init(w6.num, w6.limbNumber);
    MP_bitShiftLeft(&temp, 2);
    MP_Addition(&w5, w5, temp);
    MP_bitShiftLeft(&temp, 2);
    MP_Addition(&w5, w5, temp);
    MP_Addition(&w5, w5, w1);
    MP_exactDivXPlusXFour(w5);

    MP_Addition(&w2, w2, w6);
    MP_free(temp);
    temp = init(w0.num, w0.limbNumber);
    MP_bitShiftLeft(&temp, 6);
    MP_Addition(&w2, temp, w2);

    MP_Addition(&temp, w2, w0);
    MP_Addition(&w4, w4, temp);
    MP_free(temp);
    temp = init(w6.num, w6.limbNumber);
    MP_bitShiftLeft(&temp, 6);
    MP_Addition(&w4, w4, temp);

    MP_free(temp);
    temp = init(w5.num, w5.limbNumber);
    MP_bitShiftLeft(&temp, 1);
    MP_Addition(&w4, w4, temp); //w4 + w5*x
    MP_bitShiftLeft(&temp, 4); //w5*x^5
    MP_Addition(&w4, w4, temp); //w4 + w5*x
    MP_exactDivXtwoPlusXFour(w4);

    MP_Addition(&temp, w0, w6);
    MP_Addition(&w3, w3, temp);

    MP_Addition(&w1, w1, w3);

    MP_free(temp);
    temp = init(w1.num, w1.limbNumber);
    MP_bitShiftLeft(&temp, 1);
    temp1 = init(w3.num, w3.limbNumber);
    MP_bitShiftLeft(&temp1, 2);
    MP_Addition(&temp, temp, temp1);
    MP_Addition(&w2, w2, temp);

    MP_Addition(&temp, w4, w5);
    MP_Addition(&w3, w3, temp);

    MP_free(temp);
    temp = init(w3.num, w3.limbNumber);
    MP_bitShiftLeft(&temp, 1); //w3*x
    MP_Addition(&w1, w1, temp); //w1 + w3*x
    MP_bitShiftLeft(&temp, 1); //w3*x^2
    MP_Addition(&w1, w1, temp); //w1 + w3*x^2
    MP_exactDivXPlusXFour(w1);

    MP_Addition(&w5, w5, w1);

    MP_free(temp);
    temp = init(w5.num, w5.limbNumber);
    MP_bitShiftLeft(&temp, 1); //w5*x
    MP_Addition(&w2, temp, w2);
    MP_bitShiftLeft(&temp, 1); //w5*x^2
    MP_Addition(&w2, temp, w2);
    MP_exactDivXtwoPlusXFour(w2);

    MP_Addition(&w4, w2, w4);

    limbShiftLeft(&w1, 1 * bih);
    MP_Addition(&w, w0, w1);
    limbShiftLeft(&w2, 2 * bih);
    MP_Addition(&w, w, w2);
    limbShiftLeft(&w3, 3 * bih);
    MP_Addition(&w, w, w3);
    limbShiftLeft(&w4, 4 * bih);
    MP_Addition(&w, w, w4);
    limbShiftLeft(&w5, 5 * bih);
    MP_Addition(&w, w, w5);
    limbShiftLeft(&w6, 6 * bih);
    MP_Addition(&w, w, w6);


    MP_free(u);
    MP_free(u0);
    MP_free(u1);
    MP_free(u2);
    MP_free(u3);
    MP_free(v);
    MP_free(v0);
    MP_free(v1);
    MP_free(v2);
    MP_free(v3);
    MP_free(w0);
    MP_free(w1);
    MP_free(w2);
    MP_free(w3);
    MP_free(w4);
    MP_free(w5);
    MP_free(w6);
    MP_free(xpiuuno);
    MP_free(temp);
    MP_free(temp1);

    removeLeadingZeroLimbs(&w);

    MP_free(*result);
    *result = w;
} // end MP_toom4

/*---------------------------------------------------------------------------*/

bool isOne(MPN poly) {

    MPN x_mp = init(poly.num, poly.limbNumber);
    removeLeadingZeroLimbs(&x_mp);

    if (x_mp.limbNumber == 1 && x_mp.num[0] == 1) {
        MP_free(x_mp);
        return true;
    }

    MP_free(x_mp);
    return false;
} // end MP_Inversion_EE


/*---------------------------------------------------------------------------*/

/*
 * It eliminates leading 0s LIMBs, returning the minimum length MPN with the same value
 * if value is zero then leaves just a zeroed limb
*/
void removeLeadingZeroLimbs(MPN *poly) {
    unsigned counter = 0;
    for (int i = 0; i < poly->limbNumber - 1; ++i) {
        if (poly->num[i] == 0) {
            counter++;
        } else
            break;
    }
    MPN c = init(&poly->num[counter], poly->limbNumber - counter);
    MP_free(*poly);
    *poly = c;
} //end removeLeadingZeroLimbs

/*---------------------------------------------------------------------------*/

bool isZero(MPN poly) {

    for (int i = 0; i < poly.limbNumber; ++i) {
        if (poly.num[i] != 0)
            return false;
    }
    return true;
} // end isZero
//
/*---------------------------------------------------------------------------*/

void print(char *str, MPN poly) {

    printf("%s ", str);

    for (int i = 0; i < poly.limbNumber; ++i) {
//        printf("0x%02lx, ", poly.num[i]);
        printf("%02lx ", poly.num[i]);

    }
//    MPN new_poly = init(poly.num, poly.limbNumber);
    printf("\tDegree: %u", degree(poly));
//    MP_free(new_poly);
} // end print

/*---------------------------------------------------------------------------*/

unsigned degree(MPN poly) {

//    MPN c = init(poly.num, poly.limbNumber);
    LIMB zero_limb[] = {0};
    MPN zero = init(zero_limb, 1);
    MPN c = init_null();
    MP_Addition(&c, poly, zero);
    removeLeadingZeroLimbs(&c);

    if (isZero(c))
        return 0;

    LIMB head = c.num[0];

    if (c.limbNumber == 1) {
        for (int i = LIMB_BITS - 1; i >= 0; i--) {
            if (head >> i == 1) {
                MP_free(c);
                return (unsigned) i;
            }

        }
    }

    unsigned degree = (c.limbNumber - 1) * LIMB_BITS;
    for (int i = LIMB_BITS - 1; i >= 0; i--) {
        if (head >> i == 1) {
            MP_free(c);
            return degree + i;
        }

    }
}// end degree

/*---------------------------------------------------------------------------*/

//It returns true if a and b represent the same poly
bool MP_compare(MPN a, MPN b) {

    MPN m1 = init(a.num, a.limbNumber);
    removeLeadingZeroLimbs(&m1);
    MPN m2 = init(b.num, b.limbNumber);
    removeLeadingZeroLimbs(&m2);

    if (m1.limbNumber != m2.limbNumber) {
        MP_free(m1);
        MP_free(m2);
        return false;
    }

    for (int i = 0; i < m1.limbNumber; ++i) {
        if (m1.num[i] != m2.num[i]) {
            MP_free(m1);
            MP_free(m2);
            return false;
        }
    }
    MP_free(m1);
    MP_free(m2);

    return true;
} // end MP_compare

/*---------------------------------------------------------------------------*/