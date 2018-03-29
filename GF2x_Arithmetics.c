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

MPN init_empty(unsigned size) {
    MPN res;
    res.num = (LIMB *) calloc(size, sizeof(LIMB));
    res.limbNumber = size;
    return res;
} // end init_empty

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
//a, b are polynomial of degree <= POWER_OF_TWO
MPN MP_Addition(MPN a, MPN b) {

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
    return c;


}// end MP_addition

/*---------------------------------------------------------------------------*/

void MP_bitShiftLeft(MPN *a, int bitsToShift) {

    if (bitsToShift == 0) {
        return;
    }

    uint8_t this_carry, prev_carry;
    prev_carry = 0;


    if (a->num[0] >> LIMB_BITS - 1) { // checks if first limb bit is 1
        MPN c = init_empty(a->limbNumber + 1);
        a->num = &(MP_Addition(*a, c).num[0]);
        a->limbNumber = c.limbNumber;
        MP_free(c);
    }

    for (int i = (a->limbNumber - 1); i >= 0; --i) {

        if (a->num[i] >> LIMB_BITS - 1) // checks if first limb bit is 1
            this_carry = 1;
        else
            this_carry = 0;

        a->num[i] = a->num[i] << 1;
        if (i != (a->limbNumber - 1))
            a->num[i] = a->num[i] ^ prev_carry;
        prev_carry = this_carry;

    }

    MP_bitShiftLeft(a, bitsToShift - 1);

}// end MP_bitShiftLeft

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

MPN limbShiftLeft(MPN a, int n) {

    MPN c = init_empty(a.limbNumber + n);

    for (unsigned i = 0; i < a.limbNumber; i++) {
        c.num[i] = a.num[i];
    }

    return c;

} // end limbShiftLeft

/*---------------------------------------------------------------------------*/
//2.33
// assumption: m1, m2 are polynomial of degree <= POWER_OF_TWO, irreducible is an
// irreducible polynomial of degree POWER_OF_TWO+1

MPN MP_ShiftAndAddMul(MPN m1, MPN m2, MPN irr_poly) {

    if (irr_poly.limbNumber > T + 1) {
        fprintf(stderr, "Irr poly is too big! Aborting...\n");
        exit(EXIT_FAILURE);
    }

    MPN a, b, c;

    a = MP_Addition(m1, init_empty(T));
    b = MP_Addition(m2, init_empty(T));


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
                    b = MP_Addition(b, irr_poly);
                }
                if ((a.num[i] >> j) & 0x1)
                    c = MP_Addition(c, b);
            }

        }
    }

    MP_free(a);
    MP_free(b);
    return removeLeadingZeroLimbs(c);

}// end MP_ShiftAndAddMul

/*---------------------------------------------------------------------------*/
//2.34
//ASSUMPTION: m1, m2 limbNumb max is T

MPN MP_CombRtoLMul(MPN m1, MPN m2) {

    MPN b, c;
    b = MP_Addition(m2, init_empty(m2.limbNumber + 1));
    c = init_empty(2 * T);

    // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
    for (int k = 0; k < LIMB_BITS; ++k) {
        // j seleziona a ogni ciclo il limb
        for (int j = m1.limbNumber - 1; j >= 0; --j) {
            // shift di k posizioni (k=0 => seleziono bit più a destra)
            if (m1.num[j] >> k & 0x1) {

                for (int i = 0; i < b.limbNumber; ++i) {
                    c.num[c.limbNumber - 1 - (m1.limbNumber - 1 - j) - i] ^= b.num[b.limbNumber - 1 - i];
                }
            }
        }
        if (k != LIMB_BITS - 1)
            MP_bitShiftLeft(&b, 1);
    }

    MP_free(b);

    return removeLeadingZeroLimbs(c);

} // end MP_CombRtoLMul


/*---------------------------------------------------------------------------*/
//2.35
//ASSUMPTION: a, b limbNumb max is T
MPN MP_CombLtoRMul(MPN a, MPN b) {

    MPN c;
    c = init_empty(2 * T);

    // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
    for (int k = LIMB_BITS - 1; k >= 0; --k) {

        // j seleziona a ogni ciclo il limb
        for (int j = a.limbNumber - 1; j >= 0; --j) {

            // shift di k posizioni (k=0 => seleziono bit più a destra)
            if (a.num[j] >> k & 0x1) {

                for (int i = 0; i < b.limbNumber; ++i) {

                    c.num[c.limbNumber - 1 - (a.limbNumber - 1 - j) - i] ^= b.num[b.limbNumber - 1 - i];

                }
            }
        }
        if (k != 0)
            MP_bitShiftLeft(&c, 1);
    }

    return removeLeadingZeroLimbs(c);

} // end MP_CombLtoRMul

/*---------------------------------------------------------------------------*/
//2.36

//ASSUMPTION: a, b limbNumb max is T
//            w divisore di LIMB_BITS
MPN MP_CombLtoRMul_w(MPN a, MPN b, unsigned w) {

    MPN c = init_empty(2 * T);

    int b_u_array_size = (int) pow(2, w);
    LIMB b_u_index = 0;
    MPN b_u[b_u_array_size];

    b_u[0] = init(&b_u_index, 1);

    for (LIMB l = 1; l < b_u_array_size; ++l) {

        b_u_index = l;

        b_u[l] = MP_CombLtoRMul(b, init(&b_u_index, 1));
    }

    // k rappresenta il numero di shift in un limb
    for (int k = (LIMB_BITS / w) - 1; k >= 0; --k) {

        // j seleziona a ogni ciclo il limb
        for (int j = a.limbNumber - 1; j >= 0; --j) {

            LIMB w_bits_value = ((a.num[j] >> (k * w)) & ((LIMB) pow(2, w) - 1));

            MPN bu = b_u[w_bits_value];

            for (int i = 0; i < bu.limbNumber; ++i) {
                c.num[c.limbNumber - 1 - (a.limbNumber - 1 - j) - i] ^= bu.num[bu.limbNumber - 1 - i];
            }

        }
        if (k != 0)
            for (int l = 0; l < w; ++l) {
                MP_bitShiftLeft(&c, 1);
            }

    }

    for (LIMB l = 1; l < b_u_array_size; ++l) {

        MP_free(b_u[l]);
    }


    return removeLeadingZeroLimbs(c);

} // end MP_CombLtoRMul_w


/*---------------------------------------------------------------------------*/

MPN MP_KaratsubaMul(MPN factor1, MPN factor2) {

    MPN a = factor1;
    MPN b = factor2;
    LIMB zero_limb[] = {0x0};
    MPN zero = init(zero_limb, 1);


    if (a.limbNumber == 1 && b.limbNumber == 1) {
        return MP_CombRtoLMul(a, b);
    }

// se aggiungo zeri iniziali per raggiungere uguale lunghezza funziona

    if (a.limbNumber > b.limbNumber) {
        b = MP_Addition(init_empty(a.limbNumber), b);
    } else if (b.limbNumber > a.limbNumber) {
        a = MP_Addition(init_empty(b.limbNumber), a);
    }


    if (a.limbNumber != 1 && b.limbNumber != 1) {

        MPN first, second, third, A_01, B_01, a01perb01;

        MPN c = init_empty(1);

        MPN A_0 = init(&a.num[0], a.limbNumber - (a.limbNumber) / 2);
        MPN A_1 = init(&a.num[a.limbNumber - (a.limbNumber) / 2], (a.limbNumber) / 2);

        MPN B_0 = init(&b.num[0], b.limbNumber - (b.limbNumber) / 2);
        MPN B_1 = init(&b.num[b.limbNumber - (b.limbNumber) / 2], (b.limbNumber) / 2);

        if (isZero(A_0) || isZero(B_0))
            first = zero;
        else
            first = MP_KaratsubaMul(A_0, B_0);
        c = MP_Addition(c, first);
        for (unsigned i = 0; i < b.limbNumber - b.limbNumber % 2; i++) {
            c = limbShiftLeft(c, 1);
        }

        third = MP_KaratsubaMul(A_1, B_1);
        c = MP_Addition(c, third);

        A_01 = MP_Addition(A_0, A_1);

        B_01 = MP_Addition(B_0, B_1);

        second = MP_Addition(first, third);
        a01perb01 = MP_KaratsubaMul(A_01, B_01);
        second = MP_Addition(second, a01perb01);

        for (unsigned i = 0; i < (b.limbNumber) / 2; i++) {
            second = limbShiftLeft(second, 1);
        }

        c = MP_Addition(c, second);

        MP_free(first);
        MP_free(second);
        MP_free(third);
        MP_free(A_01);
        MP_free(B_01);
        MP_free(a01perb01);

        return c;
    }

    MPN *ptrLenIsOne, *ptrOther;
    if (a.limbNumber == 1) {
        ptrLenIsOne = &a;
        ptrOther = &b;
    } else if (b.limbNumber == 1) {
        ptrLenIsOne = &b;
        ptrOther = &a;
    }

    MPN c = init_empty(1);

    MPN A_0 = init(&(ptrLenIsOne->num[0]), 1);

    MPN B_0 = init(&(ptrOther->num[0]), ptrOther->limbNumber - (ptrOther->limbNumber) / 2);
    MPN B_1 = init(&(ptrOther->num[ptrOther->limbNumber - (ptrOther->limbNumber) / 2]), (ptrOther->limbNumber) / 2);

    MPN A0B0 = MP_KaratsubaMul(A_0, B_0);
    MPN A0B1 = MP_KaratsubaMul(A_0, B_1);

    c = MP_Addition(c, A0B0);

    for (unsigned i = 0; i < ptrOther->limbNumber; i++) {
        c = limbShiftLeft(c, 1);
    }

    c = MP_Addition(c, A0B1);

    MP_free(zero);
    MP_free(A_0);
    MP_free(B_0);
    MP_free(B_1);
    MP_free(A0B0);
    MP_free(A0B1);

    return c;


} //end MP_KaratsubaMul

/*---------------------------------------------------------------------------*/
//2.39
MPN MP_Squaring(MPN a) {

    if (!init_precomputed) {
        create_precomputed();
    }

    MPN c = init_empty(2 * a.limbNumber);

    int n = a.limbNumber;
    int n1 = sizeof(a.num[0]);
    uint8_t *a1 = (uint8_t *) a.num;
    uint16_t *c1 = (uint16_t *) c.num;
    int k = 0;
    int h;
    if (n1 == 1)
        h = 0;
    else h = n1 / 2 - 1;

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
MPN MP_Reduce(MPN a, MPN irr_poly, int powerOfTwo) {

    int block, tot_bits, extra_bits, extra_block;

    MPN c, r = copy(irr_poly);
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
        u[k] = copy(r);
        MP_bitShiftLeft(&r, 1);
    }

    tot_bits = (LIMB_BITS * a.limbNumber); //number of bitsToShift in a

    for (int l = tot_bits - 1; l >= powerOfTwo; l--) {

        block = (tot_bits - 1 - l) / LIMB_BITS;

        if (a.num[block] >> (LIMB_BITS * (1 + block) - 1 - (tot_bits - 1 - l)) & 1) {

            int j = (l - powerOfTwo) / LIMB_BITS;
            int k = (l - powerOfTwo) - LIMB_BITS * j;

            MPN u_k = u[k];

            for (int i = 0; i < u_k.limbNumber; ++i) {
                a.num[a.limbNumber - 1 - j - i] ^= u_k.num[u_k.limbNumber - 1 - i];
            }
        }
    }

    c = init_empty(T);

    extra_bits = tot_bits - powerOfTwo;
    extra_block = extra_bits / LIMB_BITS;

    LIMB mask = ~(~(0 << (extra_bits - extra_block * LIMB_BITS)) << (LIMB_BITS - extra_bits - extra_block * LIMB_BITS));

    for (int m = T - 1; m >= 0; m--) {
        if (m == 0) {
            c.num[0] = a.num[a.limbNumber - 1 - (T - 1 - m)] & mask;
        } else
            c.num[m] = a.num[a.limbNumber - 1 - (T - 1 - m)];

    }

    MP_free(r);
    for (int k = 0; k < LIMB_BITS; ++k) {
        free(&u[k]);
    }

    return removeLeadingZeroLimbs(c);
} //end MP_Reduce

/*---------------------------------------------------------------------------*/
//2.48
//Assumptions a has max degree m-1, irr_poly is an irreducible polynomial with degree m
//Inversion using extended euclidian algorithm
MPN MP_Inversion_EE(MPN a, MPN irr_poly) {

    MPN swap, shifted_v, shifted_g2;
    MPN u = copy(a);
    MPN v = copy(irr_poly);

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

        shifted_v = copy(v);
        shifted_g2 = copy(g2);

        for (int l = 0; l < j; ++l) {
            MP_bitShiftLeft(&shifted_v, 1);
            MP_bitShiftLeft(&shifted_g2, 1);
        }

        u = MP_Addition(u, shifted_v);
        g1 = MP_Addition(g1, shifted_g2);

        MP_free(shifted_g2);
        MP_free(shifted_v);
    }

    MP_free(u);
    MP_free(v);
    MP_free(g2);
    return g1;

} // end MP_Inversion_EE



/*---------------------------------------------------------------------------*/
//2.49
//Assumptions a has max degree m-1 and !=0, irr_poly is an irreducible polynomial with degree m
//binary algorithm for inversion

MPN MP_Inversion_Binary(MPN a, MPN irr_poly) {

    MPN u = copy(a);
    MPN v = copy(irr_poly);

    LIMB one[] = {1};
    LIMB zero[] = {0};

    MPN g1 = init(one, 1);
    MPN g2 = init(zero, 1);

    while (!isOne(u) && !isOne(v)) {


        while (!isZero(u) && (u.num[u.limbNumber - 1] & 1) == 0) { //z divides u

            MP_bitShiftRight(&u); // u = u/z

            if ((g1.num[g1.limbNumber - 1] & 1)) { //z doesn't divide g1
                g1 = MP_Addition(g1, irr_poly);
            }

            MP_bitShiftRight(&g1);
        }

        while (!isZero(v) && (v.num[v.limbNumber - 1] & 1) == 0) {

            MP_bitShiftRight(&v); // v = v/z

            if ((g2.num[g2.limbNumber - 1] & 1)) { //z doesn't divide g1
                g2 = MP_Addition(g2, irr_poly);
            }

            MP_bitShiftRight(&g2);
        }

        if (degree(u) > degree(v)) {

            u = MP_Addition(u, v);
            g1 = MP_Addition(g1, g2);

        } else {

            v = MP_Addition(v, u);
            g2 = MP_Addition(g1, g2);

        }

    }

    MP_free(v);

    if (isOne(u)) {
        MP_free(g2);
        MP_free(u);

        return removeLeadingZeroLimbs(g1);
    } else {
        MP_free(g1);
        MP_free(u);

        return removeLeadingZeroLimbs(g2);
    }


} // end MP_Inversion_Binary


/*---------------------------------------------------------------------------*/

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

    MPN u = copy(b);
    MPN v = copy(irr_poly);

    LIMB zero[] = {0};

    MPN g1 = copy(a);
    MPN g2 = init(zero, 1);

    while (!isOne(u) && !isOne(v)) {

        while (!isZero(u) && (u.num[u.limbNumber - 1] & 1) == 0) { //z divides u

            MP_bitShiftRight(&u); // u = u/z

            if ((g1.num[g1.limbNumber - 1] & 1)) { //z doesn't divide g1
                g1 = MP_Addition(g1, irr_poly);
            }

            MP_bitShiftRight(&g1);
        }

        while (!isZero(v) && (v.num[v.limbNumber - 1] & 1) == 0) {

            MP_bitShiftRight(&v); // v = v/z

            if ((g2.num[g2.limbNumber - 1] & 1)) { //z doesn't divide g1
                g2 = MP_Addition(g2, irr_poly);
            }

            MP_bitShiftRight(&g2);
        }

        if (degree(u) > degree(v)) {
            u = MP_Addition(u, v);
            g1 = MP_Addition(g1, g2);

        } else {
            v = MP_Addition(v, u);
            g2 = MP_Addition(g1, g2);
        }
    }

    if (isOne(u)) {
        MP_free(u);
        MP_free(v);
        MP_free(g2);

        return removeLeadingZeroLimbs(g1);
    } else {
        MP_free(u);
        MP_free(v);
        MP_free(g1);

        return removeLeadingZeroLimbs(g2);
    }

} // end MP_Division_Bin_Inv


/*---------------------------------------------------------------------------*/

void MP_exactDivOnePlusX(MPN poly) {
    LIMB t = 0;
    long i;
//    poly = removeLeadingZeroLimbs(poly);
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

MPN MP_Toom3(MPN a, MPN b) {

    MPN u = copy(a);
    MPN v = copy(b);

    if (u.limbNumber < 3 && v.limbNumber < 3) {
        return MP_CombRtoLMul(u, v);
    }

    MPN u2, u1, u0, v2, v1, v0, w, w0, w1, w2, w3, w4, u2perx2, u1perx;
    MPN *ptrMax, *ptrMin;
    LIMB xterzapiuuno_limb[] = {0x9};
    MPN xterzapiuuno = init(xterzapiuuno_limb, 1);


    if (u.limbNumber >= v.limbNumber) {
        ptrMax = &u;
        ptrMin = &v;
    } else {
        ptrMax = &v;
        ptrMin = &u;
    }

    *ptrMin = MP_Addition(init_empty(ptrMax->limbNumber), *ptrMin);

    unsigned u_limbs_div3 = u.limbNumber / 3;
    int bih;

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

    //EVALUATION

    w3 = MP_Addition(MP_Addition(u0, u1), u2);

    w2 = MP_Addition(MP_Addition(v0, v1), v2);

    w1 = MP_Toom3(w3, w2);

    u2perx2 = copy(u2); //per 0x4
    MP_bitShiftLeft(&u2perx2, 2);

    u1perx = copy(u1); //per 0x2
    MP_bitShiftLeft(&u1perx, 1);

    w0 = MP_Addition(u2perx2, u1perx);

    MPN v2perx2 = copy(v2);
    MP_bitShiftLeft(&v2perx2, 2);

    MPN v1perx = copy(v1);
    MP_bitShiftLeft(&v1perx, 1);

    w4 = MP_Addition(v2perx2, v1perx);

    w3 = MP_Addition(w3, w0);

    w2 = MP_Addition(w2, w4);

    w0 = MP_Addition(w0, u0);

    w4 = MP_Addition(w4, v0);

    w3 = MP_Toom3(w3, w2);

    w2 = MP_Toom3(w0, w4);

    w4 = MP_Toom3(u2, v2);

    w0 = MP_Toom3(u0, v0);

    //INTERPOLATION

    w3 = MP_Addition(w3, w2);

    w2 = MP_Addition(w2, w0);

    MP_bitShiftRight(&w2);
//    w2 = MP_Addition(MP_Addition(w2, w3), MP_Toom3(xterzapiuuno, w4));
    w2 = MP_Addition(MP_Addition(w2, w3), MP_CombRtoLMul(xterzapiuuno, w4));

    MP_exactDivOnePlusX(w2);

    w1 = MP_Addition(w1, w0);

    w3 = MP_Addition(w3, w1);
    MP_bitShiftRight(&w3);
    MP_exactDivOnePlusX(w3);

    w1 = MP_Addition(MP_Addition(w1, w4), w2);

    w2 = MP_Addition(w2, w3);

    w = MP_Addition(w0, limbShiftLeft(w1, 1 * bih));
    w = MP_Addition(w, limbShiftLeft(w2, 2 * bih));
    w = MP_Addition(w, limbShiftLeft(w3, 3 * bih));
    w = MP_Addition(w, limbShiftLeft(w4, 4 * bih));

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

    return removeLeadingZeroLimbs(w);
} // end MP_Toom3


/*---------------------------------------------------------------------------*/

MPN MP_Toom4(MPN a, MPN b) {

    MPN u = copy(a);
    MPN v = copy(b);

    if (u.limbNumber < 4 && v.limbNumber < 4) {
        return MP_CombRtoLMul(u, v);
    }

    MPN u3, u2, u1, u0, v3, v2, v1, v0, w, w0, w1, w2, w3, w4, w5, w6;
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

    *ptrMin = MP_Addition(init_empty(ptrMax->limbNumber), *ptrMin);


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

    w1 = MP_Addition(u3, MP_Addition(u2, MP_Addition(u1, u0)));
    w2 = MP_Addition(v3, MP_Addition(v2, MP_Addition(v1, v0)));

    w3 = MP_Toom4(w1, w2);

    MPN temp = copy(u3); //per 0x2
    MP_bitShiftLeft(&temp, 1);
    temp = MP_Addition(u2, temp);
    MP_bitShiftLeft(&temp, 1);
    w0 = MP_Addition(u1, temp);

    temp = copy(v3); //per 0x2
    MP_bitShiftLeft(&temp, 1);
    temp = MP_Addition(v2, temp);
    MP_bitShiftLeft(&temp, 1);
    w6 = MP_Addition(v1, temp);

    temp = MP_Addition(w0, (MP_Toom4(u3, xpiuuno)));
    MP_bitShiftLeft(&temp, 1);
    w4 = MP_Addition(w1, temp);

    temp = MP_Addition(w6, MP_Toom4(v3, xpiuuno));
    MP_bitShiftLeft(&temp, 1);
    w5 = MP_Addition(temp, w2);

    MP_bitShiftLeft(&w0, 1);
    w0 = MP_Addition(w0, u0);

    MP_bitShiftLeft(&w6, 1);
    w6 = MP_Addition(w6, v0);

    w5 = MP_Toom4(w5, w4);

    w4 = MP_Toom4(w6, w0);

    temp = copy(u2);
    MP_bitShiftLeft(&temp, 1);
    MPN temp1;
    temp1 = copy(u1);
    MP_bitShiftLeft(&temp1, 2);
    w0 = MP_Addition(temp, temp1);
    temp = copy(u0);
    MP_bitShiftLeft(&temp, 3); //per x^3
    w0 = MP_Addition(w0, temp);

    temp = copy(v2);
    MP_bitShiftLeft(&temp, 1);
    temp1 = copy(v1);
    MP_bitShiftLeft(&temp1, 2);
    w6 = MP_Addition(temp, temp1);
    temp = copy(v0);
    MP_bitShiftLeft(&temp, 3); //per x^3
    w6 = MP_Addition(w6, temp);

    w1 = MP_Addition(w1, w0);

    temp = copy(u0);
    MP_bitShiftLeft(&temp, 1);
    w1 = MP_Addition(w1, temp); // w1 + u0*x
    MP_bitShiftLeft(&temp, 1);
    w1 = MP_Addition(w1, temp); // w1 + u0*x^2

    w2 = MP_Addition(w2, w6);
    temp = copy(v0);
    MP_bitShiftLeft(&temp, 1);
    w2 = MP_Addition(w2, temp); // w2 + u0*x
    MP_bitShiftLeft(&temp, 1);
    w2 = MP_Addition(w2, temp); // w2 + u0*x^2

    w0 = MP_Addition(w0, u3);

    w6 = MP_Addition(w6, v3);

    w1 = MP_Toom4(w1, w2);

    w2 = MP_Toom4(w0, w6);

    w6 = MP_Toom4(u3, v3);

    w0 = MP_Toom4(u0, v0);


    //INTERPOLATION

    w1 = MP_Addition(w1, w2);
    w1 = MP_Addition(w1, w0); //+w0
    temp = copy(w0);
    MP_bitShiftLeft(&temp, 2); //+w0*x^2
    w1 = MP_Addition(w1, temp);
    MP_bitShiftLeft(&temp, 2);
    w1 = MP_Addition(w1, temp); //+w0*x^4

    w5 = MP_Addition(w5, w4);
    w5 = MP_Addition(w5, w6);
    temp = copy(w6);
    MP_bitShiftLeft(&temp, 2);
    w5 = MP_Addition(w5, temp);
    MP_bitShiftLeft(&temp, 2);
    w5 = MP_Addition(w5, temp);
    w5 = MP_Addition(w5, w1);
    MP_exactDivXPlusXFour(w5);

    w2 = MP_Addition(w2, w6);
    temp = copy(w0);
    MP_bitShiftLeft(&temp, 6);
    w2 = MP_Addition(w2, temp);

    w4 = MP_Addition(w4, MP_Addition(w2, w0));
    temp = copy(w6);
    MP_bitShiftLeft(&temp, 6);
    w4 = MP_Addition(w4, temp);

    temp = copy(w5);
    MP_bitShiftLeft(&temp, 1);
    w4 = MP_Addition(w4, temp); //w4 + w5*x
    MP_bitShiftLeft(&temp, 4); //w5*x^5
    w4 = MP_Addition(w4, temp); //w4 + w5*x
    MP_exactDivXtwoPlusXFour(w4);

    w3 = MP_Addition(w3, MP_Addition(w0, w6));

    w1 = MP_Addition(w1, w3);

    temp = copy(w1);
    MP_bitShiftLeft(&temp, 1);
    temp1 = copy(w3);
    MP_bitShiftLeft(&temp1, 2);
    w2 = MP_Addition(w2, MP_Addition(temp, temp1));

    w3 = MP_Addition(w3, MP_Addition(w4, w5));

    temp = copy(w3);
    MP_bitShiftLeft(&temp, 1); //w3*x
    w1 = MP_Addition(w1, temp); //w1 + w3*x
    MP_bitShiftLeft(&temp, 1); //w3*x^2
    w1 = MP_Addition(w1, temp); //w1 + w3*x^2
    MP_exactDivXPlusXFour(w1);

    w5 = MP_Addition(w5, w1);

    temp = copy(w5);
    MP_bitShiftLeft(&temp, 1); //w5*x
    w2 = MP_Addition(w2, temp);
    MP_bitShiftLeft(&temp, 1); //w5*x^2
    w2 = MP_Addition(w2, temp);
    MP_exactDivXtwoPlusXFour(w2);

    w4 = MP_Addition(w4, w2);

    w = MP_Addition(w0, limbShiftLeft(w1, 1 * bih));
    w = MP_Addition(w, limbShiftLeft(w2, 2 * bih));
    w = MP_Addition(w, limbShiftLeft(w3, 3 * bih));
    w = MP_Addition(w, limbShiftLeft(w4, 4 * bih));
    w = MP_Addition(w, limbShiftLeft(w5, 5 * bih));
    w = MP_Addition(w, limbShiftLeft(w6, 6 * bih));


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

    return removeLeadingZeroLimbs(w);
} // end MP_toom4

/*---------------------------------------------------------------------------*/

bool isOne(MPN mp) {

    MPN x_mp = removeLeadingZeroLimbs(mp);

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
MPN removeLeadingZeroLimbs(MPN poly) {
    unsigned counter = 0;
    for (int i = 0; i < poly.limbNumber - 1; ++i) {
        if (poly.num[i] == 0) {
            counter++;
        } else
            break;
    }
    return init(&poly.num[counter], poly.limbNumber - counter);
} //end removeLeadingZeroLimbs

/*---------------------------------------------------------------------------*/

bool isZero(MPN poly) {

    for (int i = 0; i < poly.limbNumber; ++i) {
        if (poly.num[i] != 0)
            return false;
    }
    return true;
} // end isZero

/*---------------------------------------------------------------------------*/

void print(char *str, MPN poly) {

    printf("%s ", str);

    for (int i = 0; i < poly.limbNumber; ++i) {
        printf("0x%02lx, ", poly.num[i]);
    }

    printf("\tDegree: %u", degree(poly));
} // end print

/*---------------------------------------------------------------------------*/

unsigned degree(MPN poly) {

    MPN c = removeLeadingZeroLimbs(copy(poly));

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

MPN copy(MPN poly) {
    return MP_Addition(init_empty(poly.limbNumber), poly);
}// end copy


/*---------------------------------------------------------------------------*/

//It returns true if a and b represent the same poly
bool MP_compare(MPN a, MPN b) {

    MPN m1 = removeLeadingZeroLimbs(a);
    MPN m2 = removeLeadingZeroLimbs(b);

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
