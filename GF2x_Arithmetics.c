
#include <assert.h>
#include "GF2x_Arithmetics.h"

static inline unsigned lead_zero_limbs_count(MPN poly) {
    unsigned counter = 0;
    for (int i = 0; i < poly.limbNumber; ++i) {
        if (poly.num[i] == 0) {
            counter++;
        } else
            break;
    }
    return counter;
}


static inline void sum_in_first_arg(MPN a, MPN b) {
    int offset = (a).limbNumber - (b).limbNumber;
    for (int i = 0; i < (b).limbNumber; i++) {

        (a).num[offset + i] = (a).num[offset + i] ^ (b).num[i];

    }
}


static inline void bitShiftLeft(MPN a, unsigned bitsToShift) {
    int j;
    LIMB mask = ~(((LIMB) 0x01 << (LIMB_BITS - (bitsToShift))) - 1);
    for (j = 0; j < (a).limbNumber - 1; j++) {
        (a).num[j] <<= (bitsToShift);
        (a).num[j] |= ((a).num[j + 1] & mask) >> (LIMB_BITS - bitsToShift);
    }
    (a).num[j] <<= (bitsToShift);
}


uint16_t precomputed[256];

bool init_precomputed = 0;

void create_precomputed() {
    for (unsigned j = 0; j < 256; ++j) {

        uint8_t temp = (uint8_t) j;
        precomputed[j] = (uint16_t) (0 + (temp & 0x1));

        for (unsigned i = 1; i < 8; ++i) {
            temp = temp >> 1;
            precomputed[j] = (uint16_t) (precomputed[j] + (temp & 1) * (2, 2 * i));

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
    MPN res;
    res.num = (LIMB *) malloc(sizeA * sizeof(LIMB));
    res.limbNumber = sizeA;
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


    MPN c;

    if (a.limbNumber > b.limbNumber) {
        ALLOCA_EMPTY(c, a.limbNumber); //c = init_empty(a.limbNumber);

        for (int i = 0; i < b.limbNumber; i++) {
            c.num[a.limbNumber - b.limbNumber + i] = a.num[a.limbNumber - b.limbNumber + i] ^ b.num[i];
        }
        for (int i = 0; i < a.limbNumber - b.limbNumber; i++) {
            c.num[i] = a.num[i];
        }
    } else {
        ALLOCA_EMPTY(c, b.limbNumber); //c = init_empty(b.limbNumber);
        for (int i = 0; i < a.limbNumber; i++) {
            c.num[b.limbNumber - a.limbNumber + i] = b.num[b.limbNumber - a.limbNumber + i] ^ a.num[i];
        }
        for (int i = 0; i < b.limbNumber - a.limbNumber; i++) {
            c.num[i] = b.num[i];
        }

    }


    MP_free(*result);
    *result = init(c.num, c.limbNumber);

}// end MP_addition

/*---------------------------------------------------------------------------*/


void MP_bitShiftLeft_checkSize(MPN *a, int bitsToShift) {


    if (bitsToShift == 0) {
        return;
    }

    if (a->limbNumber == 0) return;

    assert(bitsToShift < LIMB_BITS);
    int leading_zeros = 0;

    for (int i = LIMB_BITS - 1; i >= LIMB_BITS - bitsToShift; i--) {

        if (a->num[0] >> i & 1) { //cerca posizione primo bit
            break;

        } else {
            leading_zeros++;
        }
    }
//    printf("\nlead: %d",leading_zeros);


    if (leading_zeros < bitsToShift) { // checks if first limb bit is 1

//        MPN c = init_empty(a->limbNumber + 1);
//        MP_Addition(a, *a, c);
        MPN c;
        ALLOCA_EMPTY(c, a->limbNumber + 1)
        sum_in_first_arg(c, *a);
        MP_free(*a);

        *a = init(c.num, c.limbNumber);

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

static inline void MP_bitShiftRight(MPN *a) {

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

static inline void limbShiftLeft(MPN *a, int n) {

    int counter = lead_zero_limbs_count(*a);
    if (counter >= n) {
        for (int j = 0; j < a->limbNumber - n; ++j) {
            a->num[j] = a->num[j + n];
        }

        for (int k = a->limbNumber - n; k < a->limbNumber; k++) {
            a->num[k] = 0;
        }
        return;
    }

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


    MPN a, b, c;
    ALLOCA_EMPTY(a, T);
    ALLOCA_EMPTY(b, T);


    sum_in_first_arg(a, factor1);
    sum_in_first_arg(b, factor2);


    unsigned shiftToHigherOne = (LIMB_BITS - S);

    // trovo valore da controllare poi su b
    // (sarebbe la posizione che sfora di uno il grado e a cui addiziono il polinomio irr

    for (int i = (int) (irr_poly.limbNumber - 1); i >= 0; --i) {

        for (unsigned j = 0; j < LIMB_BITS; ++j) {

// initial setting of c
            if (i == (int) (irr_poly.limbNumber - 1) && j == 0) {
                if (a.num[a.limbNumber - 1] & 0x1) {
                    ALLOCA(c, b.num, irr_poly.limbNumber); //c = init(b.num, irr_poly.limbNumber);
                } else {
                    ALLOCA_EMPTY(c, irr_poly.limbNumber); //c = init_empty(irr_poly.limbNumber);
                }

            } else {

                MP_bitShiftLeft_checkSize(&b, 1);
                if (b.num[0] >> shiftToHigherOne) {
                    sum_in_first_arg(b, irr_poly);//MP_Addition(&b, b, irr_poly);
                }
                if ((a.num[i] >> j) & 0x1) sum_in_first_arg(c, b); //MP_Addition(&c, c, b);
            }

        }
    }

    MP_free(*result);
    *result = init(c.num, c.limbNumber);

}// end MP_ShiftAndAddMul

/*---------------------------------------------------------------------------*/

//2.34
//ASSUMPTION: m1, m2 limbNumb max is T
void MP_CombRtoLMul(MPN *result, MPN factor1, MPN factor2) {

    MPN b;
    MPN c;

//    MPN b = init_null();
//    MP_Addition(&b, factor2, init_empty(factor2.limbNumber + 1));

    ALLOCA_EMPTY(b, (factor2.limbNumber + 1));
    sum_in_first_arg(b, factor2);
//    c = init_empty(2 * T);
//    ALLOCA_EMPTY(c,(2*T))
    if (factor1.limbNumber > factor2.limbNumber) {
        ALLOCA_EMPTY(c, (2 * factor1.limbNumber));
    } else ALLOCA_EMPTY(c, (2 * factor2.limbNumber));
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
        if (k != LIMB_BITS - 1) bitShiftLeft(b, 1);
    }

//    unsigned counter = 0;
//
//    lead_zero_limbs_count(&counter, c);


    MP_free(*result);
    // = init(&c.num[counter], c.limbNumber - counter);
    *result = init(c.num, c.limbNumber);


} // end MP_CombRtoLMul


/*---------------------------------------------------------------------------*/
//2.35
//ASSUMPTION: a, b limbNumb max is T
void MP_CombLtoRMul(MPN *result, MPN factor1, MPN factor2) {

    MPN c;
//    c = init_empty(2 * T);
//    ALLOCA_EMPTY(c, (2 * T));
    if (factor1.limbNumber > factor2.limbNumber) {
        ALLOCA_EMPTY(c, (2 * factor1.limbNumber));
    } else ALLOCA_EMPTY(c, (2 * factor2.limbNumber));
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
        if (k != 0) {
            bitShiftLeft(c, 1);
        }
//            MP_bitShiftLeft_checkSize(&c, 1); //non sfora mai


    }
    MP_free(*result);
    *result = init(c.num, c.limbNumber);


} // end MP_CombLtoRMul

/*---------------------------------------------------------------------------*/
//2.36

//ASSUMPTION: a, b limbNumb max is T
//            w divisore di LIMB_BITS

void MP_CombLtoRMul_w(MPN *res, MPN factor1, MPN factor2, unsigned w) {


    MPN a, b, c;


    if (factor1.limbNumber > factor2.limbNumber) {
        a = factor1;
        ALLOCA_EMPTY(b, factor1.limbNumber)//= init_empty(factor1.limbNumber);
        sum_in_first_arg(b, factor2);
        ALLOCA_EMPTY(c, 2 * factor1.limbNumber)


    } else {
//        a = init_empty(factor2.limbNumber);
        b = factor2;
        ALLOCA_EMPTY(a, factor2.limbNumber)
        sum_in_first_arg(a, factor1);
        ALLOCA_EMPTY(c, 2 * factor2.limbNumber)

    }

//    print("\na: ",a);
//    print("\nb: ",b);



//    c = init_empty(2 * T);

//    ALLOCA_EMPTY(c, 2 * T)


    int b_u_array_size = 1 << w;//(int) pow(2, w);
//    LIMB b_u_index = 0;
    MPN b_u[b_u_array_size];

//    b_u[0] = init(&b_u_index, 1);
    ALLOCA_EMPTY(b_u[0], 1)
    b_u[0].num[0] = 0;
    MPN cc;
//    cc = init_empty(2 * T);
    ALLOCA_EMPTY(cc, (2 * b.limbNumber));
    MPN bubu;// = init(&b_u_index, 1);
    ALLOCA_EMPTY(bubu, 1)
    for (int l = 1; l < b_u_array_size; ++l) {

//        b_u_index = (LIMB) l;

//        b_u[l] = init_null();
        bubu.num[0] = (LIMB) l;;


//      ----------------- MP_CombLtoRMul(&b_u[l], b, init(&b_u_index, 1)) -----------------


        // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
        for (int k = LIMB_BITS - 1; k >= 0; --k) {

            // j seleziona a ogni ciclo il limb
            for (int j = b.limbNumber - 1; j >= 0; --j) {

                // shift di k posizioni (k=0 => seleziono bit più a destra)
                if (b.num[j] >> k & 0x1) {

                    for (int i = 0; i < bubu.limbNumber; ++i) {

                        cc.num[cc.limbNumber - 1 - (b.limbNumber - 1 - j) - i] ^= bubu.num[bubu.limbNumber - 1 -
                                                                                           i];

                    }
                }
            }
            if (k != 0) {
                bitShiftLeft(cc, 1);
            }
//                MP_bitShiftLeft_checkSize(&cc, 1); //non sfora mai
        }
//        MP_free(b_u[l]);
//        b_u[l] = init(cc.num, cc.limbNumber);


        //      ----------------- MP_CombLtoRMul(&b_u[l], b, init(&b_u_index, 1)) -----------------
        int counter = lead_zero_limbs_count(cc);
        ALLOCA_EMPTY(b_u[l], cc.limbNumber - counter);
        for (int m = counter; m < cc.limbNumber; ++m) {
            b_u[l].num[m - counter] = cc.num[m];
        }
//        removeLeadingZeroLimbs(&b_u[l]);
        sum_in_first_arg(cc, cc);
    }


    // k rappresenta il numero di shift in un limb
    for (int k = (LIMB_BITS / w) - 1; k >= 0; --k) {
        // j seleziona a ogni ciclo il limb
        for (int j = a.limbNumber - 1; j >= 0; --j) {


            LIMB w_bits_value = ((a.num[j] >> (k * w)) & ((LIMB) (1 << w) - 1));

            MPN bu = b_u[w_bits_value];

            for (int i = 0; i < bu.limbNumber; ++i) {
                c.num[c.limbNumber - 1 - (a.limbNumber - 1 - j) - i] ^= bu.num[bu.limbNumber - 1 - i];
            }


        }
        if (k != 0) {
            bitShiftLeft(c, w);
        }
//            MP_bitShiftLeft_checkSize(&c, w);


    }
    MP_free(*res);
    *res = init(c.num, c.limbNumber);


} // end MP_CombLtoRMul_w
/*---------------------------------------------------------------------------*/

void karatsuba(MPN *restrict c, MPN *restrict factor1, MPN *restrict factor2) {

    int counter1 = lead_zero_limbs_count(*factor1), counter2 = lead_zero_limbs_count(*factor2);

    if (counter1 == (*factor1).limbNumber && counter2 == (*factor2).limbNumber) {
        sum_in_first_arg(*c, *c);
        return;
    }

    if ((*factor1).limbNumber <= KARATSUBA_MIN_LIMBS && (*factor2).limbNumber <= KARATSUBA_MIN_LIMBS) {

        // ---------------------MP_CombRtoLMul---------------------

        MPN b;

        ALLOCA_EMPTY(b, ((*factor2).limbNumber + 1));
        sum_in_first_arg(b, (*factor2));
        // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
        for (int k = 0; k < LIMB_BITS; ++k) {
            // j seleziona a ogni ciclo il limb
            for (int j = (*factor1).limbNumber - 1; j >= 0; --j) {
                // shift di k posizioni (k=0 => seleziono bit più a destra)
                if ((*factor1).num[j] >> k & 0x1) {

                    for (int i = 0; i < b.limbNumber; ++i) {
                        c->num[c->limbNumber - 1 - ((*factor1).limbNumber - 1 - j) - i] ^= b.num[b.limbNumber - 1 - i];
                    }
                }
            }
            if (k != LIMB_BITS - 1)
                // MP_bitShiftLeft_checkSize(&b, 1);
                bitShiftLeft(b, 1);

        }

        // ----------------------end MP_CombRtoLMul----------------

        return;

    }

    MPN a;
    MPN b;
    MPN zero;
    unsigned c_limbs = c->limbNumber;

    ALLOCA_EMPTY(zero, 1)


    if ((*factor1).limbNumber - counter1 > (*factor2).limbNumber - counter2) {
//        a = (*factor1);
        ALLOCA(a, &(*factor1).num[counter1], (*factor1).limbNumber - counter1)
//        b = init_empty((*factor1).limbNumber);
        ALLOCA_EMPTY(b, (*factor1).limbNumber - counter1)
        for (int i = 0, j = 0; i < b.limbNumber && j < (*factor2).limbNumber; ++i, ++j) {
            b.num[b.limbNumber - 1 - i] = (*factor2).num[(*factor2).limbNumber - 1 - j];
        }

    } else {

        ALLOCA_EMPTY(a, (*factor2).limbNumber - counter2)
        for (int i = 0, j = 0; i < a.limbNumber && j < (*factor1).limbNumber; ++i, ++j) {
            a.num[a.limbNumber - 1 - i] = (*factor1).num[(*factor1).limbNumber - 1 - j];
        }


        ALLOCA(b, &(*factor2).num[counter2], (*factor2).limbNumber - counter2)

    }


    if (a.limbNumber != 1 && b.limbNumber != 1) {

        MPN first, second, third, a01perb01, A_0, A_1, B_0, B_1;

        ALLOCA_EMPTY(first, c_limbs)
        ALLOCA_EMPTY(third, c_limbs)
        ALLOCA_EMPTY(a01perb01, c_limbs);


        A_0.num = &a.num[0];
        A_0.limbNumber = (a.limbNumber - (a.limbNumber) / 2);
        A_1.num = &a.num[a.limbNumber - (a.limbNumber) / 2];
        A_1.limbNumber = a.limbNumber / 2;
        B_0.num = &b.num[0];
        B_0.limbNumber = (b.limbNumber - (b.limbNumber / 2));
        B_1.num = &b.num[b.limbNumber - (b.limbNumber) / 2];
        B_1.limbNumber = b.limbNumber / 2;


        if (isZero(A_0) || isZero(B_0))
            first = zero; //ok,tanto non è mai uno store per risultato
        else
            karatsuba(&first, &A_0, &B_0);

        sum_in_first_arg((*c), first);

        //        ------------------ limbshiftLeft -----------------------
        unsigned shift = b.limbNumber - b.limbNumber % 2;
        for (int j = 0; j < c->limbNumber - shift; ++j) {
            c->num[j] = c->num[j + shift];
        }

        for (int k = c->limbNumber - shift; k < c->limbNumber; k++) {
            c->num[k] = 0;
        }
//       ------------------ end limbshiftLeft --------------------

        karatsuba(&third, &A_1, &B_1);

        sum_in_first_arg(A_0, A_1);
        sum_in_first_arg(B_0, B_1);

        ALLOCA(second, third.num, c_limbs)

        sum_in_first_arg(second, first);

        karatsuba(&a01perb01, &A_0, &B_0);


        sum_in_first_arg(second, a01perb01);

        //        ------------------ limbshiftLeft -----------------------
        shift = (b.limbNumber) / 2;
        for (int j = 0; j < second.limbNumber - shift; ++j) {
            second.num[j] = second.num[j + shift];
        }

        for (int k = second.limbNumber - shift; k < second.limbNumber; k++) {
            second.num[k] = 0;
        }
//       ------------------ end limbshiftLeft --------------------

        sum_in_first_arg((*c), third);
        sum_in_first_arg((*c), second);
    }


} //end karatsuba

void MP_KaratsubaMul(MPN *result, MPN factor1, MPN factor2) {

    if (factor1.limbNumber <= KARATSUBA_MIN_LIMBS && factor2.limbNumber <= KARATSUBA_MIN_LIMBS) {
        MP_CombRtoLMul(result, factor1, factor2);
    }

    MPN c;

    if (factor1.limbNumber > factor2.limbNumber) {
        ALLOCA_EMPTY(c, 2 * factor1.limbNumber);

    } else {
        ALLOCA_EMPTY(c, 2 * factor2.limbNumber);
    }

    karatsuba(&c, &factor1, &factor2);

    signed counter = 0;
    for (int i = 0; i < c.limbNumber - 1; ++i) {
        if (c.num[i] == 0) {
            counter++;
        } else
            break;
    }

    MP_free(*result);
    *result = init(&c.num[counter], c.limbNumber - counter);
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

    r.num[limb] = r.num[limb] ^ (LIMB) (1 << temp);

// Precomputation of z^k * r(z)
    for (int k = 0; k < LIMB_BITS; ++k) {
        u[k] = init(r.num, r.limbNumber);
        MP_bitShiftLeft_checkSize(&r, 1);
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
            MP_bitShiftLeft_checkSize(&shifted_v, 1);
            MP_bitShiftLeft_checkSize(&shifted_g2, 1);
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

static inline void MP_exactDivOnePlusX(MPN poly) {
    LIMB t = 0;
    long i;

    int counter = lead_zero_limbs_count(poly);
    if (poly.limbNumber == counter) {
        return;
    }

    for (i = poly.limbNumber - 1; i >= counter; i--) {

        t ^= poly.num[i];

        for (int j = 1; j <= LIMB_BITS / 2; j = j * 2) {
            t ^= t << j;
        }
        poly.num[i] = t;
        t >>= LIMB_BITS - 1;
    }

} // end MP_exactDivOnePlusX


/*---------------------------------------------------------------------------*/
static inline void MP_exactDivXPlusXFour(MPN c) {


    LIMB t = 0;
    long i;
    unsigned shift;

    int counter = lead_zero_limbs_count(c);
    MPN reverse;
    if (c.limbNumber == counter) {
        return;
    }
    ALLOCA_EMPTY(reverse, c.limbNumber - counter)


    for (int j = 0, k = c.limbNumber - 1; j < c.limbNumber - counter; k--, ++j) {
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


    sum_in_first_arg(c, c);

    for (int j = counter, k = reverse.limbNumber - 1; j < c.limbNumber; k--, ++j) {
        c.num[j] = reverse.num[k];
    }


} // end MP_exactDivXPlusXFour


/*---------------------------------------------------------------------------*/

static inline void MP_exactDivXtwoPlusXFour(MPN poly) {

    LIMB cy = 0, t;
    long i;

//    MPN reverse = init_empty(poly.limbNumber);


    MPN reverse;


    int counter = lead_zero_limbs_count(poly);

    if (poly.limbNumber == counter) {
        return;
    }
    ALLOCA_EMPTY(reverse, poly.limbNumber - counter)
    for (int j = 0, k = poly.limbNumber - 1; j < poly.limbNumber - counter; k--, ++j) {
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

    sum_in_first_arg(poly, poly);
    for (int j = counter, k = reverse.limbNumber - 1; j < poly.limbNumber; k--, ++j) {
        poly.num[j] = reverse.num[k];
    }

//    print("\nrev: ", reverse);
//    print("\npoly: ", poly);

} //end MP_exactDivXtwoPlusXFour

/*---------------------------------------------------------------------------*/

void toom3(MPN *restrict result, MPN *restrict factor1, MPN *restrict factor2) {


    PRINTF(("\n------toom3-------"));

    MPN u, v;

    int counter1 = lead_zero_limbs_count(*factor1), counter2 = lead_zero_limbs_count(*factor2);

    if (counter1 == (*factor1).limbNumber && counter2 == (*factor2).limbNumber) {
        sum_in_first_arg(*result, *result);
        return;
    }

    if ((*factor1).limbNumber - counter1 < TOOM_MIN_LIMBS && (*factor2).limbNumber - counter2 < TOOM_MIN_LIMBS) {

        // ---------------------MP_CombRtoLMul---------------------

        MPN b;
        MPN c;

        ALLOCA_EMPTY(c, result->limbNumber)

        ALLOCA_EMPTY(b, ((*factor2).limbNumber - counter2 + 1));
//        sum_in_first_arg(b, (*factor2));
        for (int j = 0, i = 0; j < b.limbNumber && i < (*factor2).limbNumber - counter2; ++j, ++i) {
            b.num[b.limbNumber - 1 - j] = (*factor2).num[(*factor2).limbNumber - 1 - i];
        }

        // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
        for (int k = 0; k < LIMB_BITS; ++k) {
            // j seleziona a ogni ciclo il limb
            for (int j = (*factor1).limbNumber - 1; j >= 0; --j) {
                // shift di k posizioni (k=0 => seleziono bit più a destra)
                if ((*factor1).num[j] >> k & 0x1) { //OKKK!!

                    for (int i = 0; i < b.limbNumber; ++i) {
                        c.num[c.limbNumber - 1 - ((*factor1).limbNumber - 1 - j) - i] ^= b.num[b.limbNumber - 1 - i];
                    }
                }
            }
            if (k != LIMB_BITS - 1)
//                MP_bitShiftLeft_checkSize(&b, 1);
                bitShiftLeft(b, 1);
        }


        unsigned counter = lead_zero_limbs_count(c);

        sum_in_first_arg(*result, *result); //azzero contenuto di result
        sum_in_first_arg(*result, c);


        // ----------------------end MP_CombRtoLMul----------------

        PRINTF(("\n----end------"));

        return;
    }


    MPN u2, u1, u0, v2, v1, v0;


    unsigned factor_limbs_div3;
    unsigned bih; //number of limbs for each part
    int check;


    if ((*factor1).limbNumber - counter1 > (*factor2).limbNumber - counter2) {

        factor_limbs_div3 = ((*factor1).limbNumber - counter1) / 3;

        check = ((*factor1).limbNumber - counter1);

    } else {
        factor_limbs_div3 = ((*factor2).limbNumber - counter2) / 3;

        check = (*factor2).limbNumber - counter2;

    }


    if (factor_limbs_div3 * 3 == check) {

        bih = factor_limbs_div3;


    } else {

        bih = factor_limbs_div3 + 1;


    }


    ALLOCA_EMPTY(u, 3 * bih)
    for (int j = 0, i = 0; j < u.limbNumber && i < (*factor1).limbNumber; ++j, ++i) {
        u.num[u.limbNumber - 1 - j] = (*factor1).num[(*factor1).limbNumber - 1 - i];
    }

    ALLOCA_EMPTY(v, 3 * bih)
    for (int j = 0, i = 0; j < v.limbNumber && i < (*factor2).limbNumber; ++j, ++i) {
        v.num[v.limbNumber - 1 - j] = (*factor2).num[(*factor2).limbNumber - 1 - i];
    }

    u2.num = &(u.num[0]);
    u2.limbNumber = bih;
    u1.num = &(u.num[bih]);
    u1.limbNumber = bih;
    u0.num = &(u.num[2 * bih]);
    u0.limbNumber = bih;


    v2.num = &(v.num[0]);
    v2.limbNumber = bih;
    v1.num = &(v.num[bih]);
    v1.limbNumber = bih;
    v0.num = &(v.num[2 * bih]);
    v0.limbNumber = bih;

    T3(("\nu: ", u));
    T3(("\nv: ", v));
    T3(("\nresult: ", *result));


    T3(("\nu0: ", u0));
    T3(("\nu1: ", u1));
    T3(("\nu2: ", u2));


    T3(("\nv0: ", v0));
    T3(("\nv1: ", v1));
    T3(("\nv2: ", v2));


    MPN w;
    MPN w0, w1, w2, w3, w4;

    ALLOCA_EMPTY(w0, 4 * bih)
    ALLOCA_EMPTY(w1, 4 * bih)
    ALLOCA_EMPTY(w2, 4 * bih)
    ALLOCA_EMPTY(w3, 4 * bih)
    ALLOCA_EMPTY(w4, 4 * bih)

    MPN xterzapiuuno;
    ALLOCA_EMPTY(xterzapiuuno, 4 * bih)
    xterzapiuuno.num[xterzapiuuno.limbNumber - 1] = 0x9;


    T3(("\nw0: ", w0));
    T3(("\nw1: ", w1));
    T3(("\nw2: ", w2));
    T3(("\nw3: ", w3));
    T3(("\nw4: ", w4));

    //EVALUATION


    //    ----------------------------------- w3 -----------------------------------

    sum_in_first_arg(w3, u0);
    sum_in_first_arg(w3, u1);
    sum_in_first_arg(w3, u2);

    T3(("\nw3: ", w3));

    //    ----------------------------------- w2 -----------------------------------

    sum_in_first_arg(w2, v0);
    sum_in_first_arg(w2, v1);
    sum_in_first_arg(w2, v2);

    T3(("\nw2: ", w2));


    //    ----------------------------------- w1 -----------------------------------

//    MP_Toom3(&w1, w3, w2);


    toom3(&w1, &w3, &w2);

    T3(("\nw1: ", w1));


    MPN u2perx2;
    ALLOCA_EMPTY(u2perx2, u2.limbNumber + 1);
    sum_in_first_arg(u2perx2, u2);
    bitShiftLeft(u2perx2, 2);

    MPN u1perx;
    ALLOCA_EMPTY(u1perx, u1.limbNumber + 1);
    sum_in_first_arg(u1perx, u1);
    bitShiftLeft(u1perx, 1);

    T3(("\nu2perx2: ", u2perx2));
    T3(("\nu1perx: ", u1perx));


    //    ----------------------------------- w0 -----------------------------------


    sum_in_first_arg(w0, u2perx2);
    sum_in_first_arg(w0, u1perx);

    T3(("\nw0: ", w0));


    MPN v2perx2;
    ALLOCA_EMPTY(v2perx2, v2.limbNumber + 1)
    sum_in_first_arg(v2perx2, v2);
    bitShiftLeft(v2perx2, 2);

    MPN v1perx;
    ALLOCA_EMPTY(v1perx, v1.limbNumber + 1)
    sum_in_first_arg(v1perx, v1);
    bitShiftLeft(v1perx, 1);

    //    ----------------------------------- w4 -----------------------------------


    sum_in_first_arg(w4, v2perx2);
    sum_in_first_arg(w4, v1perx);


    T3(("\nw4: ", w4));

    sum_in_first_arg(w3, w0);

    T3(("\nw3: ", w3));

    sum_in_first_arg(w2, w4);


    T3(("\nw2: ", w2));

    sum_in_first_arg(w0, u0);

    T3(("\nw0: ", w0));

    sum_in_first_arg(w4, v0);


    toom3(&w3, &w3, &w2);
    T3(("\n---------w3: ", w3));

    toom3(&w2, &w0, &w4);

    T3(("\nw2: ", w2));


    toom3(&w4, &u2, &v2);
    T3(("\nw4: ", w4));

    toom3(&w0, &u0, &v0);

    T3(("\nw0: ", w0));


    //INTERPOLATION

    sum_in_first_arg(w3, w2);
    T3(("\nw3: ", w3));


    sum_in_first_arg(w2, w0);
    T3(("\nw2: ", w2));


    MP_bitShiftRight(&w2);
    T3(("\nw2: ", w2));

    sum_in_first_arg(w2, w3);

    toom3(&xterzapiuuno, &xterzapiuuno, &w4);

    sum_in_first_arg(w2, xterzapiuuno);

    T3(("\nAA w2: ", w2));


    MP_exactDivOnePlusX(w2);
    T3(("\nw2: ", w2));

    T3(("\nboh w1: ", w1));
    T3(("\nboh w0: ", w0));

    sum_in_first_arg(w1, w0);
    T3(("\nw1: ", w1));


    sum_in_first_arg(w3, w1);
    T3(("\nw1: ", w1));
    T3(("\nw3: ", w3));


    MP_bitShiftRight(&w3);
    T3(("\nw3: ", w3));

    MP_exactDivOnePlusX(w3);
    T3(("\nw3: ", w3));


    sum_in_first_arg(w1, w4);
    sum_in_first_arg(w1, w2);

    T3(("\nw1: ", w1));


    sum_in_first_arg(w2, w3);


    T3(("\nw2: ", w2));


    sum_in_first_arg(*result, *result);
    T3(("\nresult: ", *result));

    sum_in_first_arg(*result, w0);
    T3(("\nresult: ", *result));



//
//    T3(("\nresult: ", *result));

    PRINTF(("\n----end------"));

//
//    w = init_null();

//
    T3(("\nw0: ", w0));
    T3(("\nw1: ", w1));
    T3(("\nw2: ", w2));
    T3(("\nw3: ", w3));
    T3(("\nw4: ", w4));


    int counter = lead_zero_limbs_count(w1);
    for (int l = 0; l < w1.limbNumber - counter; ++l) {
        result->num[(result->limbNumber) - l - 1 - bih] ^= w1.num[w1.limbNumber - 1 - l];
    }
    T3(("\nresult: ", *result));

    counter = lead_zero_limbs_count(w2);
    for (int l = 0; l < w2.limbNumber - counter; ++l) {
        result->num[(result->limbNumber) - l - 1 - 2 * bih] ^= w2.num[w2.limbNumber - 1 - l];
    }
    T3(("\nresult: ", *result));

    counter = lead_zero_limbs_count(w3);
    for (int l = 0; l < w3.limbNumber - counter; ++l) {
        result->num[(result->limbNumber) - l - 1 - 3 * bih] ^= w3.num[w3.limbNumber - 1 - l];
    }
    T3(("\nresult: ", *result));

    counter = lead_zero_limbs_count(w4);
    T3(("\nw4: ", w4));


    PRINTF(("\ncounter: %d", counter));
    for (int l = 0; l < w4.limbNumber - counter; ++l) {
        result->num[(result->limbNumber) - l - 1 - 4 * bih] ^= w4.num[w4.limbNumber - 1 - l];
    }

    T3(("\nresult: ", *result));

} // end MP_Toom3


void MP_Toom3(MPN *result, MPN factor1, MPN factor2) {
    PRINTF(("\n------tooom3NEW-------"));
    T3(("\nfactor1: ", factor1));
    T3(("\nfactor2: ", factor2));


//    MPN u = init(factor1.num, factor1.limbNumber), v = init(factor2.num, factor2.limbNumber);
//

    if (factor1.limbNumber < TOOM_MIN_LIMBS && factor2.limbNumber < TOOM_MIN_LIMBS) {
        MP_CombRtoLMul(result, factor1, factor2);
        return;
    }

    MPN partial_result;


    INIT_TO_FIT_MUL(partial_result, factor1, factor2)

    T3(("\npar_res: ", partial_result));
    toom3(&partial_result, &factor1, &factor2);
//    toom3(result, factor1, factor2);


    MP_free(*result);
    *result = init(partial_result.num, partial_result.limbNumber);
} // end MP_Toom3


/*---------------------------------------------------------------------------*/

void toom4(MPN *restrict result, MPN *restrict factor1, MPN *restrict factor2) {

    PRINTF(("\n------tooom4-------"));

    MPN u, v, t;

    int counter1 = lead_zero_limbs_count(*factor1), counter2 = lead_zero_limbs_count(*factor2);

    if (counter1 == (*factor1).limbNumber && counter2 == (*factor2).limbNumber) {
        sum_in_first_arg(*result, *result);
        return;
    }


    if ((*factor1).limbNumber - counter1 < TOOM_MIN_LIMBS && (*factor2).limbNumber - counter2 < TOOM_MIN_LIMBS) {
        // ---------------------MP_CombRtoLMul---------------------
        MPN b;
        MPN c;

        ALLOCA_EMPTY(c, result->limbNumber)

        ALLOCA_EMPTY(b, ((*factor2).limbNumber - counter2 + 1));
//        sum_in_first_arg(b, (*factor2));
        for (int j = 0, i = 0; j < b.limbNumber && i < (*factor2).limbNumber - counter2; ++j, ++i) {
            b.num[b.limbNumber - 1 - j] = (*factor2).num[(*factor2).limbNumber - 1 - i];
        }

        // k rappresenta il numero di shift per selezionare il bit da controllare in ogni LIMB
        for (int k = 0; k < LIMB_BITS; ++k) {
            // j seleziona a ogni ciclo il limb
            for (int j = (*factor1).limbNumber - 1; j >= 0; --j) {
                // shift di k posizioni (k=0 => seleziono bit più a destra)
                if ((*factor1).num[j] >> k & 0x1) { //OKKK!!

                    for (int i = 0; i < b.limbNumber; ++i) {
                        c.num[c.limbNumber - 1 - ((*factor1).limbNumber - 1 - j) - i] ^= b.num[b.limbNumber - 1 - i];
                    }
                }
            }
            if (k != LIMB_BITS - 1) bitShiftLeft(b, 1);
//                MP_bitShiftLeft_checkSize(&b, 1);
        }

        unsigned counter = lead_zero_limbs_count(c);


//        *result = init(c.num, c.limbNumber);
//
        sum_in_first_arg(*result, *result); //azzero contenuto di result
        sum_in_first_arg(*result, c);

//        ALLOCA(*result,c.num,c.limbNumber) // non va

        // ----------------------end MP_CombRtoLMul----------------

        PRINTF(("\n----end------"));

        return;
    }
    PRINTF(("\n------INIT-------"));


    T4(("\nu: ", u));
    T4(("\nv: ", v));
    T4(("\nresult: ", *result));

    MPN u3, u2, u1, u0, v3, v2, v1, v0, w, w0, w1, w2, w3, w4, w5, w6;


    MPN xpiuuno;
    ALLOCA_EMPTY(xpiuuno, 1);
    xpiuuno.num[0] = 0x3;


    unsigned factor_limbs_div4;
    unsigned bih; //number of limbs for each part
    int check;


    if ((*factor1).limbNumber - counter1 > (*factor2).limbNumber - counter2) {

        factor_limbs_div4 = ((*factor1).limbNumber - counter1) / 4;

        check = ((*factor1).limbNumber - counter1);

    } else {
        factor_limbs_div4 = ((*factor2).limbNumber - counter2) / 4;

        check = (*factor2).limbNumber - counter2;

    }

    if (factor_limbs_div4 * 4 == check) {

        bih = factor_limbs_div4;

    } else {

        bih = factor_limbs_div4 + 1;

    }


    ALLOCA_EMPTY(u, 4 * bih)
    for (int j = 0, i = 0; j < u.limbNumber && i < (*factor1).limbNumber; ++j, ++i) {
        u.num[u.limbNumber - 1 - j] = (*factor1).num[(*factor1).limbNumber - 1 - i];
    }

    ALLOCA_EMPTY(v, 4 * bih)
    for (int j = 0, i = 0; j < v.limbNumber && i < (*factor2).limbNumber; ++j, ++i) {
        v.num[v.limbNumber - 1 - j] = (*factor2).num[(*factor2).limbNumber - 1 - i];
    }

    u3.num = &(u.num[0]);
    u3.limbNumber = bih;
    u2.num = &(u.num[bih]);
    u2.limbNumber = bih;
    u1.num = &(u.num[2 * bih]);
    u1.limbNumber = bih;
    u0.num = &(u.num[3 * bih]);
    u0.limbNumber = bih;

    v3.num = &(v.num[0]);
    v3.limbNumber = bih;
    v2.num = &(v.num[bih]);
    v2.limbNumber = bih;
    v1.num = &(v.num[2 * bih]);
    v1.limbNumber = bih;
    v0.num = &(v.num[3 * bih]);
    v0.limbNumber = bih;




    PRINTF(("\nfactor_limbs_div4: %d", factor_limbs_div4));
    PRINTF(("\nbih: %d", bih));


    T4(("\nu: ", u));
    T4(("\nv: ", v));

    T4(("\nu0: ", u0));
    T4(("\nu1: ", u1));
    T4(("\nu2: ", u2));


    T4(("\nv0: ", v0));
    T4(("\nv1: ", v1));
    T4(("\nv2: ", v2));
    MPN temp, temp1;
    ALLOCA_EMPTY(temp, 4 * bih)
    ALLOCA_EMPTY(w0, 4 * bih)
    ALLOCA_EMPTY(w1, 4 * bih)
    ALLOCA_EMPTY(w2, 4 * bih)
    ALLOCA_EMPTY(w3, 4 * bih)
    ALLOCA_EMPTY(w4, 4 * bih)
    ALLOCA_EMPTY(w5, 4 * bih)
    ALLOCA_EMPTY(w6, 4 * bih)



    //EVALUATION
//    MP_Addition(&w1, u1, u0);
    sum_in_first_arg(w1, u1);
    sum_in_first_arg(w1, u0);

    T4(("\nw1 ", w1));

//    MP_Addition(&w1, u2, w1);
    sum_in_first_arg(w1, u2);
    T4(("\nw1 ", w1));
//    MP_Addition(&w1, u3, w1);
    sum_in_first_arg(w1, u3);
    T4(("\nw1 ", w1));

//    MP_Addition(&w2, v1, v0);
//    T4(("\nw2 ", w2));
//    MP_Addition(&w2, v2, w2);
//    T4(("\nw2 ", w2));
//    MP_Addition(&w2, v3, w2);

    sum_in_first_arg(w2, v1);
    sum_in_first_arg(w2, v0);
    sum_in_first_arg(w2, v2);
    sum_in_first_arg(w2, v3);
    T4(("\nw2 ", w2));


    toom4(&w3, &w1, &w2);

    T4(("\nw0: ", w0));
    T4(("\nw1: ", w1));
    T4(("\nw2: ", w2));
    T4(("\nw3: ", w3));
    T4(("\nw4: ", w4));
    T4(("\nw5: ", w5));
    T4(("\nw6: ", w6));
    PRINTF(("\n-------------"));

    T4(("\nw3 ", w3));


//    MPN temp = init(u3.num, u3.limbNumber); //per 0x2


    sum_in_first_arg(temp, u3);
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);
    T4(("\ntemp ", temp));


//    MP_Addition(&temp, u2, temp);
    sum_in_first_arg(temp, u2);
    T4(("\ntemp ", temp));
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));
//    MP_Addition(&w0, u1, temp);
    sum_in_first_arg(w0, u1);
    sum_in_first_arg(w0, temp);
    T4(("\n\nLAST EDIT w0: ", w0));




//    temp = init(v3.num, v3.limbNumber); //per 0x2
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, v3);

//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);
    T4(("\ntemp ", temp));



//    MP_Addition(&temp, v2, temp);

    sum_in_first_arg(temp, v2);
    T4(("\ntemp ", temp));


//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);
    T4(("\ntemp ", temp));

    sum_in_first_arg(w6, w6);
    sum_in_first_arg(w6, v1);
    sum_in_first_arg(w6, temp);
//    MP_Addition(&w6, v1, temp);
    T4(("\nw6 ", w6));



//    print("\npretwmp: ",temp);
    toom4(&temp, &u3, &xpiuuno);
    T4(("\ntemp ", temp));

//    print("\nw0: ",w0);
//    print("\nw1: ",w1);
//    print("\nw2: ",w2);
//    print("\ntwmp: ",temp);






    sum_in_first_arg(temp, w0);
//    MP_Addition(&temp, w0, temp);
    T4(("\ntemp ", temp));
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));


    sum_in_first_arg(w4, w4);
    sum_in_first_arg(w4, w1);

    sum_in_first_arg(w4, temp);
//    MP_Addition(&w4, w1, temp);
    T4(("\nw4 ", w4));


    toom4(&temp, &v3, &xpiuuno);
    T4(("\ntemp ", temp));
    sum_in_first_arg(temp, w6);
//    MP_Addition(&temp, w6, temp);
    T4(("\ntemp ", temp));
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);
    T4(("\ntemp ", temp));

    sum_in_first_arg(w5, w5);
    sum_in_first_arg(w5, temp);
    sum_in_first_arg(w5, w2);
//    MP_Addition(&w5, temp, w2);
    T4(("\nw5 ", w5));


//    MP_bitShiftLeft_checkSize(&w0, 1);
    bitShiftLeft(w0, 1);

//    if (w0.num[0] != 0)
//        print("\n", w0);

    T4(("\nw0 ", w0));


    sum_in_first_arg(w0, u0);
//    MP_Addition(&w0, u0, w0);
    T4(("\nw0 ", w0));

//    MP_bitShiftLeft_checkSize(&w6, 1);
    bitShiftLeft(w6, 1);

    T4(("\nw6 ", w6));

    sum_in_first_arg(w6, v0);
//    MP_Addition(&w6, v0, w6);
    T4(("\nw6 ", w6));


    toom4(&w5, &w5, &w4);
    T4(("\nw5 ", w5));


    toom4(&w4, &w6, &w0);
    T4(("\nw4 ", w4));


//    temp = init(u2.num, u2.limbNumber);

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, u2);
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));


//    MP_Addition(&w0, temp, temp1);
    sum_in_first_arg(w0, w0);
    sum_in_first_arg(w0, temp);


//    MPN temp1;
//    ALLOCA_EMPTY(temp1,4*bih)
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, u1);
//    temp1 = init(u1.num, u1.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 2);
    bitShiftLeft(temp, 2);

//    T4(("\ntemp1 ", temp1));

    sum_in_first_arg(w0, temp);
    T4(("\nw0 ", w0));

//    temp = init(u0.num, u0.limbNumber);
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, u0);
//    MP_bitShiftLeft_checkSize(&temp, 3); //per x^3
    bitShiftLeft(temp, 3);

    T4(("\ntemp ", temp));

//    MP_Addition(&w0, temp, w0);
    sum_in_first_arg(w0, temp);
    T4(("\nw0 ", w0));

//    temp = init(v2.num, v2.limbNumber);
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, v2);
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w6, w6);
    sum_in_first_arg(w6, temp);

//    temp1 = init(v1.num, v1.limbNumber);
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, v1);

//    MP_bitShiftLeft_checkSize(&temp, 2);
    bitShiftLeft(temp, 2);

//    T4(("\ntemp1 ", temp1));

//    MP_Addition(&w6, temp, temp1);

    sum_in_first_arg(w6, temp);
    T4(("\nw6 ", w6));


//    temp = init(v0.num, v0.limbNumber);
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, v0);
//    MP_bitShiftLeft_checkSize(&temp, 3); //per x^3
    bitShiftLeft(temp, 3);
    T4(("\ntemp ", temp));

//    MP_Addition(&w6, temp, w6);
    sum_in_first_arg(w6, temp);

    T4(("\nw6 ", w6));

    sum_in_first_arg(w1, w0);
//    MP_Addition(&w1, w0, w1);
    T4(("\nw1 ", w1));

//    MP_free(temp);
//    temp = init(u0.num, u0.limbNumber);
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, u0);
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);
    T4(("\ntemp ", temp));

    sum_in_first_arg(w1, temp);
//    MP_Addition(&w1, temp, w1); // w1 + u0*x
    T4(("\nw1 ", w1));

//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w1, temp);
//    MP_Addition(&w1, w1, temp); // w1 + u0*x^2
    T4(("\nw1 ", w1));

    sum_in_first_arg(w2, w6);
//    MP_Addition(&w2, w6, w2);
    T4(("\nw2 ", w2));

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, v0);
//    temp = init(v0.num, v0.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w2, temp);
//    MP_Addition(&w2, temp, w2); // w2 + u0*x
    T4(("\nw2 ", w2));
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);
    T4(("\ntemp ", temp));

    sum_in_first_arg(w2, temp);
//    MP_Addition(&w2, temp, w2); // w2 + u0*x^2
    T4(("\nw2 ", w2));

    sum_in_first_arg(w0, u3);
//    MP_Addition(&w0, u3, w0);
    T4(("\nw0 ", w0));

    sum_in_first_arg(w6, v3);
//    MP_Addition(&w6, v3, w6);
    T4(("\nw6 ", w6));

    toom4(&w1, &w1, &w2);
    T4(("\nw1 ", w1));

    toom4(&w2, &w0, &w6);
    T4(("\nw2 ", w2));

    toom4(&w6, &u3, &v3);
    T4(("\nw6 ", w6));

    toom4(&w0, &u0, &v0);
    T4(("\nw0 ", w0));


    PRINTF(("\nINTERPOLATION"));

    //INTERPOLATION

    sum_in_first_arg(w1, w2);
//    MP_Addition(&w1, w2, w1);
    T4(("\nw1 ", w1));
    sum_in_first_arg(w1, w0);
//    MP_Addition(&w1, w0, w1); //+w0
    T4(("\nw1 ", w1));

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w0);
//    temp = init(w0.num, w0.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 2); //+w0*x^2
    bitShiftLeft(temp, 2);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w1, temp);
//    MP_Addition(&w1, temp, w1);
    T4(("\nw1 ", w1));
//    MP_bitShiftLeft_checkSize(&temp, 2);
    bitShiftLeft(temp, 2);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w1, temp);
//    MP_Addition(&w1, temp, w1); //+w0*x^4
    T4(("\nw1 ", w1));

    sum_in_first_arg(w5, w4);
//    MP_Addition(&w5, w4, w5);
    T4(("\nw5 ", w5));
    sum_in_first_arg(w5, w6);
//    MP_Addition(&w5, w6, w5);
    T4(("\nw5 ", w5));

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w6);
//    temp = init(w6.num, w6.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 2);
    bitShiftLeft(temp, 2);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w5, temp);
//    MP_Addition(&w5, w5, temp);
    T4(("\nw5 ", w5));
//    MP_bitShiftLeft_checkSize(&temp, 2); ***
    bitShiftLeft(temp, 2);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w5, temp);
//    MP_Addition(&w5, w5, temp);
    T4(("\nw5 ", w5));
    sum_in_first_arg(w5, w1);
//    MP_Addition(&w5, w5, w1);
    T4(("\nw5 ", w5));
    MP_exactDivXPlusXFour(w5);
    T4(("\nw5 ", w5));

    sum_in_first_arg(w2, w6);
//    MP_Addition(&w2, w2, w6);
    T4(("\nw2 ", w2));

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w0);
//    temp = init(w0.num, w0.limbNumber);
    //****************************

//    MP_bitShiftLeft_checkSize(&temp, 6);
    bitShiftLeft(temp, 6);

    T4(("\ntemp ", temp));
    //****************************

    sum_in_first_arg(w2, temp);
//    MP_Addition(&w2, temp, w2);
    T4(("\nw2 ", w2));

    sum_in_first_arg(w4, w2);
    sum_in_first_arg(w4, w0);
//    MP_Addition(&temp, w2, w0);
//    T4(("\ntemp ", temp));

//    MP_Addition(&w4, w4, temp);
    T4(("\nw4 ", w4));
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w6);
//    MP_free(temp);
//    temp = init(w6.num, w6.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 6);
    bitShiftLeft(temp, 6);

    T4(("\ntemp ", temp));


    sum_in_first_arg(w4, temp);
//    MP_Addition(&w4, w4, temp);
    T4(("\nw4 ", w4));

//    MP_free(temp);
//    temp = init(w5.num, w5.limbNumber);
    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w5);
    T4(("\ntemp ", temp));

//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w4, temp);
//    MP_Addition(&w4, w4, temp); //w4 + w5*x
    T4(("\nw4 ", w4));

//    MP_bitShiftLeft_checkSize(&temp, 4); //w5*x^5
    bitShiftLeft(temp, 4);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w4, temp);
//    MP_Addition(&w4, w4, temp); //w4 + w5*x
    T4(("\nw4 ", w4));


    MP_exactDivXtwoPlusXFour(w4);
    T4(("\nw4 ", w4));

    sum_in_first_arg(w3, w0);
    sum_in_first_arg(w3, w6);
//    MP_Addition(&temp, w0, w6);

//    MP_Addition(&w3, w3, temp);
    T4(("\nw3 ", w3));

    sum_in_first_arg(w1, w3);
//    MP_Addition(&w1, w1, w3);
    T4(("\nw1 ", w1));

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w1);
//    MP_free(temp);
//    temp = init(w1.num, w1.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 1);
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w2, temp);

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w3);

//    temp1 = init(w3.num, w3.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 2);
    bitShiftLeft(temp, 2);

//    T4(("\ntemp1 ", temp1));
    sum_in_first_arg(w2, temp);

//    MP_Addition(&temp, temp, temp1);
//    T4(("\ntemp ", temp));
//    MP_Addition(&w2, w2, temp);
//    T4(("\nw2 ", w2));



//    MP_Addition(&temp, w4, w5);
//    T4(("\ntemp ", temp));
//    MP_Addition(&w3, w3, temp);
    sum_in_first_arg(w3, w4);
    sum_in_first_arg(w3, w5);
    T4(("\nw3 ", w3));

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w3);
//    MP_free(temp);
//    temp = init(w3.num, w3.limbNumber);

//    MP_bitShiftLeft_checkSize(&temp, 1); //w3*x
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w1, temp);
//    MP_Addition(&w1, w1, temp); //w1 + w3*x
    T4(("\nw1 ", w1));
//    MP_bitShiftLeft_checkSize(&temp, 1); //w3*x^2
    bitShiftLeft(temp, 1);

    sum_in_first_arg(w1, temp);
//    MP_Addition(&w1, w1, temp); //w1 + w3*x^2
    T4(("\nw1 ", w1));
    MP_exactDivXPlusXFour(w1);
    T4(("\nw1 ", w1));

    sum_in_first_arg(w5, w1);
//    MP_Addition(&w5, w5, w1);
    T4(("\nw5 ", w5));

    sum_in_first_arg(temp, temp);
    sum_in_first_arg(temp, w5);
//    temp = init(w5.num, w5.limbNumber);
//    MP_bitShiftLeft_checkSize(&temp, 1); //w5*x
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w2, temp);
//    MP_Addition(&w2, temp, w2);
    T4(("\nw2 ", w2));
//    MP_bitShiftLeft_checkSize(&temp, 1); //w5*x^2
    bitShiftLeft(temp, 1);

    T4(("\ntemp ", temp));

    sum_in_first_arg(w2, temp);
//    MP_Addition(&w2, temp, w2);
    T4(("\nw2 ", w2));
    MP_exactDivXtwoPlusXFour(w2);
    T4(("\nw2 ", w2));

    sum_in_first_arg(w4, w2);
//    MP_Addition(&w4, w2, w4);
    T4(("\nw4 ", w4));

    PRINTF(("\n-------------"));
    T4(("\nw0: ", w0));
    T4(("\nw1: ", w1));
    T4(("\nw2: ", w2));
    T4(("\nw3: ", w3));
    T4(("\nw4: ", w4));
    T4(("\nw5: ", w5));
    T4(("\nw6: ", w6));
    PRINTF(("\n-------------"));


    ALLOCA_EMPTY(w, result->limbNumber)
//    sum_in_first_arg(w, w0);

    int counter = lead_zero_limbs_count(w0);
    for (int l = 0; l < w0.limbNumber - counter; ++l) {
        w.num[(w.limbNumber) - l - 1] ^= w0.num[w0.limbNumber - 1 - l];
    }
    counter = lead_zero_limbs_count(w1);
    for (int l = 0; l < w1.limbNumber - counter; ++l) {
        w.num[(w.limbNumber) - l - 1 - bih] ^= w1.num[w1.limbNumber - 1 - l];
    }
    T4(("\nw: ", w));


    counter = lead_zero_limbs_count(w2);
    for (int l = 0; l < w2.limbNumber - counter; ++l) {
        w.num[(w.limbNumber) - l - 1 - 2 * bih] ^= w2.num[w2.limbNumber - 1 - l];
    }
    T4(("\nw: ", w));


    counter = lead_zero_limbs_count(w3);
    for (int l = 0; l < w3.limbNumber - counter; ++l) {
        w.num[(w.limbNumber) - l - 1 - 3 * bih] ^= w3.num[w3.limbNumber - 1 - l];
    }
    T4(("\nw: ", w));


    counter = lead_zero_limbs_count(w4);
//    PRINTF(("\ncounter: %d", counter));
    for (int l = 0; l < w4.limbNumber - counter; ++l) {
        w.num[(w.limbNumber) - l - 1 - 4 * bih] ^= w4.num[w4.limbNumber - 1 - l];
    }

    T4(("\nw: ", w));

    counter = lead_zero_limbs_count(w5);
    PRINTF(("\ncounter: %d", counter));
    for (int l = 0; l < w5.limbNumber - counter; ++l) {
        w.num[(w.limbNumber) - l - 1 - 5 * bih] ^= w5.num[w5.limbNumber - 1 - l];
    }

    T4(("\nw: ", w));


    counter = lead_zero_limbs_count(w6);
    PRINTF(("\ncounter: %d", counter));
    for (int l = 0; l < w6.limbNumber - counter; ++l) {
        w.num[(w.limbNumber) - l - 1 - 6 * bih] ^= w6.num[w6.limbNumber - 1 - l];
    }

    T4(("\nw: ", w));

    PRINTF(("\n-------FINAL------"));

    sum_in_first_arg(*result, *result);
    sum_in_first_arg(*result, w);
}


void MP_Toom4(MPN *result, MPN factor1, MPN factor2) {

    if (factor1.limbNumber < TOOM_MIN_LIMBS && factor2.limbNumber < TOOM_MIN_LIMBS) {
        MP_CombRtoLMul(result, factor1, factor2);
        return;
    }


    PRINTF(("\n------tooom4NEW-------"));
    T4(("\nfactor1: ", factor1));
    T4(("\nfactor2: ", factor2));

    MPN partial_result;
    INIT_TO_FIT_MUL(partial_result, factor1, factor2)

    T4(("\npar_res: ", partial_result));
    toom4(&partial_result, &factor1, &factor2);


    MP_free(*result);
    *result = init(partial_result.num, partial_result.limbNumber);


} // end MP_toom4

/*---------------------------------------------------------------------------*/

static inline bool isOne(MPN poly) {



//    MPN x_mp = init(poly.num, poly.limbNumber);
//    removeLeadingZeroLimbs(&x_mp);



//    if (x_mp.limbNumber == 1 && x_mp.num[0] == 1) {
//        MP_free(x_mp);
//        return true;
//    }
//
//    MP_free(x_mp);
//    return false;


    int counter = lead_zero_limbs_count(poly);

    if (poly.limbNumber - counter == 1 && poly.num[poly.limbNumber - 1] == 1)
        return true;

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
    if (counter != 0) {
        MPN c = init(&poly->num[counter], poly->limbNumber - counter);
        MP_free(*poly);
        *poly = c;
        return;
    }

} //end removeLeadingZeroLimbs

/*---------------------------------------------------------------------------*/

static inline bool isZero(MPN poly) {

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

    printf("\tDegree: %u", degree(poly));
} // end print

/*---------------------------------------------------------------------------*/

unsigned degree(MPN poly) {

//    MPN c = init(poly.num, poly.limbNumber);
//    removeLeadingZeroLimbs(&c);

    unsigned counter = lead_zero_limbs_count(poly);

    if (counter == poly.limbNumber)
        return 0;

//    LIMB head = c.num[0];

    LIMB head = poly.num[counter];
    if (poly.limbNumber - counter == 1) {
        for (int i = LIMB_BITS - 1; i >= 0; i--) {
            if (head >> i == 1) {
//                MP_free(c);
                return (unsigned) i;
            }

        }
    }

    unsigned degree = (poly.limbNumber - 1 - counter) * LIMB_BITS;
    for (int i = LIMB_BITS - 1; i >= 0; i--) {
        if (head >> i == 1) {
            //   MP_free(c);
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