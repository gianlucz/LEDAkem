/*----------------------------------------------------------------------------*/
/*
 * Elements of GF(2)[x] are stored in compact dense binary form.
 *
 * Each bit in a byte is assumed to be the coefficient of a binary
 * polynomial f(x), in Big-Endian format (i.e., reading everything from
 * left to right, the most significant element is met first):
 *
 * byte:(0000 0000) == 0x00 ... f(x) == 0
 * byte:(0000 0001) == 0x01 ... f(x) == 1
 * byte:(0000 0010) == 0x02 ... f(x) == x
 * byte:(0000 0011) == 0x03 ... f(x) == x+1
 * ...                      ... ...
 * byte:(0000 1111) == 0x0F ... f(x) == x^{3}+x^{2}+x+1
 * ...                      ... ...
 * byte:(1111 1111) == 0xFF ... f(x) == x^{7}+x^{6}+x^{5}+x^{4}+x^{3}+x^{2}+x+1
 *
 *
 * A "machine word" (A_i) is considered as a DIGIT.
 * Bytes in a DIGIT are assumed in Big-Endian format:
 * E.g., if sizeof(DIGIT) == 4:
 * A_i: A_{i,3} A_{i,2} A_{i,1} A_{i,0}.
 * A_{i,3} denotes the most significant byte, A_{i,0} the least significant one.
 * f(x) ==   x^{31} + ... + x^{24} +
 *         + x^{23} + ... + x^{16} +
 *         + x^{15} + ... + x^{8}  +
 *         + x^{7}  + ... + x^{0}
 *
 *
 * Multi-precision elements (i.e., with multiple DIGITs) are stored in
 * Big-endian format:
 *           A = A_{n-1} A_{n-2} ... A_1 A_0
 *
 *           position[A_{n-1}] == 0
 *           position[A_{n-2}] == 1
 *           ...
 *           position[A_{1}]  ==  n-2
 *           position[A_{0}]  ==  n-1
 */
/*----------------------------------------------------------------------------*/



#define DIGIT_SIZE_b 64
#define w (DIGIT_SIZE_b)
#define NUM_BITS_GF2X_ELEMENT (P) //grado del polinomio
#define m (2*(NUM_BITS_GF2X_ELEMENT +1) / w)
#define NUM_DIGITS_GF2X_MODULUS ((NUM_BITS_GF2X_ELEMENT+1+DIGIT_SIZE_b-1)/DIGIT_SIZE_b)

#include <x86intrin.h>
#include <wmmintrin.h>
#include <immintrin.h>
#include <pmmintrin.h>
#include <string.h>
#include <assert.h>


void gf2x_add(const int nr, DIGIT Res[],
              const int na, const DIGIT A[],
              const int nb, const DIGIT B[])
{
  __m128i a, b;

 for (unsigned i = 0; i < nr/2; i++){
     a = _mm_lddqu_si128( (__m128i *)A + i );
     b = _mm_lddqu_si128( (__m128i *)B + i );

     _mm_storeu_si128(((__m128i *)Res + i), _mm_xor_si128(a, b));
  }

  if(nr%2 != 0){
      Res[nr-1] = A[nr-1] ^ B[nr-1];
  }
 }


/*From : https://graphics.stanford.edu/~seander/bithacks.html#IntegerLog
given that v is a power of 2*/

int higherBitSet(DIGIT v)
{
    static const DIGIT b[] = {0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC,
         0xF0F0F0F0F0F0F0F0, 0xFF00FF00FF00FF00,
         0xFFFF0000FFFF0000, 0xFFFFFFFF00000000}
    unsigned int r = (v & b[0]) != 0;

        r |= ((v & b[5]) != 0) << 5;
        r |= ((v & b[4]) != 0) << 4;
        r |= ((v & b[3]) != 0) << 3;
        r |= ((v & b[2]) != 0) << 2;
        r |= ((v & b[1]) != 0) << 1;

    return r;
}


// H1=((x 0) (0 1))
void multByH1(DIGIT h00, DIGIT h01, DIGIT h10, DIGIT h11)
{
    DIGIT r00, r01, r10, r11;

    r00 = h00 << 1;
    r01 = h01 << 1;
    r10 = h10;
    r11 = h11;

    h00 = r00; h01 = r01; h10 = r10; h11 = r11;
}

// H2=((x x) (1 0))
void multByH2(DIGIT h00, DIGIT h01, DIGIT h10, DIGIT h11)
{
    DIGIT r00, r01, r10, r11;

    r00 = (h00 << 1) ^ (h10 << 1);
    r01 = (h01 << 1) ^ (h11 << 1);
    r10 = h00;
    r11 = h01;

    h00 = r00; h01 = r01; h10 = r10; h11 = r11;
}

// H3=((0 x) (1 0))
void multByH3(DIGIT h00, DIGIT h01, DIGIT h10, DIGIT h11)
{
    DIGIT r00, r01, r10, r11;

    r00 =  h10 << 1;
    r01 =  h11 << 1;
    r10 = h00;
    r11 = h01;

    h00 = r00; h01 = r01; h10 = r10; h11 = r11;
}

// H4=((1 0) (x x))
void multByH4(DIGIT h00, DIGIT h01, DIGIT h10, DIGIT h11)
{
    DIGIT r00, r01, r10, r11;

    r00 = h00;
    r01 = h01;
    r10 = (h00 << 1) ^ (h10 << 1);
    r11 = (h01 << 1) ^ (h11 << 1);

    h00 = r00; h01 = r01; h10 = r10; h11 = r11;
}

// H5=((1 0) (0 x))
void multByH5(DIGIT h00, DIGIT h01, DIGIT h10, DIGIT h11)
{
    DIGIT r00, r01, r10, r11;

    r00 = h00;
    r01 = h01;
    r10 = h01 << 1;
    r11 = h11 << 1;

    h00 = r00; h01 = r01; h10 = r10; h11 = r11;
}



void multi_single_mult(DIGIT in[], DIGIT out[], DIGIT h_0, DIGIT h_1, int imm)
{
    int l = m-2;
    __m128i h, y1, y2, y3, y4, y5;
    _m64 xr0, x1, x2; // h1, h2;

//    h0 = _mm_lddqu_si64(h_0);
//    h1 = _mm_lddqu_si64(h_1);

    h = _mm_lddqu_si128(_mm_set_epi64((_m64)h1,(_m64)h2));

    y1 = _mm_lddqu_si128((__m128i *)&in[l]);
    y2 = _mm_lddqu_si128((__m128i *)&in[l] - 1);

    xr0 = _mm_extract_epi64 (y3, 0); //store the lo bits of the first clmul result
    _mm_storeu_epi64(&in[m-1], xr0);


    y3 =_mm_clmulepi64_si128(y1, h, imm+0); //R(0)
    y4 =_mm_clmulepi64_si128(y1, h, imm+1); //R(1)
    y5 =_mm_clmulepi64_si128(y2, h, imm+0); //R(2)


    x1 = _mm_extract_epi64(y3, 1); //hi bits of R(0)
    x2 = _mm_extract_epi64(y5, 0); //lo bits of R(2)
    xr0 = _mm_extract_epi64(y5, 1); //hi bits of R(2), passed to the loop


    y4 = _mm_xor_si128(y4, _mm_set_epi64(x2, x1));
    _mm_storeu_si128((__m128i *)&in[l-1], y4);


    for(l= l-4; l > 0; l = l-2){ /*condizione di uscita????*/
        y1 = _mm_lddqu_si128((__m128i *)&in[l]);

        y3 =_mm_clmulepi64_si128(y1, h, imm+0); //R(i)
        y4 =_mm_clmulepi64_si128(y1, h, imm+1); //R(i+1)

        x2 = _mm_extract_epi64(y4, 0); //lo bits of R(i+1)

        y3 = _mm_xor_si128(y3, _mm_set_epi64(x2, xr0));

        _mm_storeu_si128((__m128i *)&in[l], y3);

        xr0 = _mm_extract_epi64(y4, 1); //hi bits of R(i+1), passed to the next iteration
    }
    if(l == 0){
        y1 = _mm_lddqu_si128((__m128i *)&in[l]);

        x1 = _mm_extract_epi64(y1, 0); //hi bits of R(i)

        _mm_storeu_epi64(&in[l], _mm_xor_si64(x1, xr0));

        xr0 = _mm_extract_epi64(y1, 1); //lo bits of R(i+2)
    }
    _mm_storeu_epi64(&in[l], xr0);

}

static
void left_bits_shifting(const int length, DIGIT in[], DIGIT out[], int amount)
{
   int j;
   __m128i a,b;


   for(j = 0; j < (length-1)/2; j++){

     a = _mm_lddqu_si128( (__m128i *)&in[0] + j );//load in[j] and in[j+1]
     b = _mm_lddqu_si128( (__m128i *)&in[1] + j );  //load in[j+1] and in[j+2]

     a = _mm_slli_epi64(a, amount);
     b = _mm_srli_epi64(b, (DIGIT_SIZE_b-amount));

     _mm_storeu_si128(((__m128i *)&out[0] + j), _mm_or_si128(a, b));

   }

    for(j = j*2; j < length-1; j++) {
     in[j] <<= amount;                    /* logical shift does not need clearing */
     in[j] |= in[j+1] >> (DIGIT_SIZE_b-amount);
   }

   in[length-1] <<= amount; //last element shift
}



/* Execution time it's not constant: may vary due to some optimization for
*  calculating the matrix H(x) and the multi-word per single word multiplication.
*
* Based on: An Algorithm for Inversion in GF(2m) Suitable for Implementation Using
* a Polynomial Multiply Instruction on GF(2).
*
* Katsuki Kobayashi, Naofumi Takagi, and Kazuyoshi Takagi.
*/
void inverse(DIGIT out[], const DIGIT in[]){
    DIGIT v[2*NUM_DIGITS_GF2X_ELEMENT] = {0}, // V(x)
                u[2*NUM_DIGITS_GF2X_ELEMENT] = {0}, // U(x)
                    s[2*NUM_DIGITS_GF2X_ELEMENT] = {0}, // S(x)
                        r[2*NUM_DIGITS_GF2X_ELEMENT] = {0}; // R(x)

    u[NUM_DIGITS_GF2X_ELEMENT-1] = 0x1;
    v[NUM_DIGITS_GF2X_ELEMENT-1] = 0x0;


    DIGIT c, d; //C(x),D(x)
    DIGIT h00, h01, h10, h11; // matrix H(x)

    int shift_amount = 0;
    int deg_r = NUM_BITS_GF2X_ELEMENT;
    int deg_s = NUM_BITS_GF2X_ELEMENT;

    DIGIT mask = 0x1;
    int i,j;

    for (i = NUM_DIGITS_GF2X_MODULUS-1; i >= 1 ; i--) s[i] = in[i];

    //what we divide it's x^P +1  for our polynomial
    v[0] = 0x7FFFFFFFFFFFFFFF; // x^P
    v[NUM_DIGITS_GF2X_ELEMENT-1] = 0x1; // + 1

    while (deg_r > 0) {
        c = r[0]; //R(m-1)
        d = s[0];

        if(c == 0){ //C(x) = 0
            __m128i y1,y2;

            for(j = 0; j<m-1; j= j+2){ // may use memmove( dest* , source*, bytes);
                y1 = _mm_lddqu_si128((__m128i *)&r[j+1]);
                y2 = _mm_lddqu_si128((__m128i *)&s[j+1]);
                _mm_storeu_si128((__m128i *)&r[j], y1);
                _mm_storeu_si128((__m128i *)&s[j], y2);
            }
            if(j == m-1){
                r[m-2] = r[m-1];
                s[m-2] = s[m-1];
            }
            r[m-1] = 0x0;
            s[m-1] = 0x0;

            deg_r -= w;
        }else{ //define H(X)
            h00 = 0x1;
            h01 = 0x0;
            h10 = 0x0;
            h11 = 0x1;
            j = 1;

            while(j < w && deg_r > 0){
                j++;
                if(c & mask == 0){
                    c << 1;
                    multByH1(h00, h01, h10, h11);
                    deg_r --;
                }else{
                    if(deg_r == deg_s){
                        deg_r--;
                        if(d & mask == 1){
                            DIGIT tmp = c;
                            c = c ^ d; //xor
                            c << 1;
                            d = tmp;

                            multByH2(h00, h01, h10, h11);
                        }else{
                            DIGIT tmp = c;
                            c = d << 1;
                            d = tmp;

                            multByH3(h00, h01, h10, h11);
                        }//endif
                    }
                    else{
                        deg_s--;
                        if(d & mask == 1){
                            d = c ^ d;
                            d << 1;

                            multByH4(h00, h01, h10, h11);
                        }else{
                            d << 1;

                            multByH5(h00, h01, h10, h11);
                        }//endif
                    }//endif
                }//endif
            }//end while

            //(R(x) S(x))*H(x) and (U(x) V(x)) * H(x)

            r_t[2*NUM_DIGITS_GF2X_ELEMENT] = {0},
                s_t[2*NUM_DIGITS_GF2X_ELEMENT] = {0},
                    u_t[2*NUM_DIGITS_GF2X_ELEMENT] = {0},
                        v_t[2*NUM_DIGITS_GF2X_ELEMENT] = {0},
                            tmp[2*NUM_DIGITS_GF2X_ELEMENT] = {0};


            if(h00 == 0){
                r_t = {0};
                u_t = {0};
                tmp = {0};
            }else if(popcnt_u64(h00) == 1){
                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, r, r_t, higherBitSet(h00));
                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, u, u_t, higherBitSet(h00));
            }else{
                multi_single_mult(r, r_t, h00, h01, 0);
                multi_single_mult(u, u_t, h00, h01, 0);
            } //end h00

            if (h01 == 0){
                //do nothing
            }else if(popcnt_u64(h01) == 1){
                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, s, tmp, higherBitSet(h01)); //??
                r_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, r_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, r_t);

                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, v, tmp, higherBitSet(h01));
                u_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, u_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, u_t);

            }else{ //use r_t and u_t as temporary register to store the intermediate passage
                multi_single_mult(s, tmp, h00, h01, 16);
                r_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, r_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, r_t);

                multi_single_mult(v, tmp, h00, h01 16);
                u_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, u_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, u_t);
            }//end h01


            if (h10 == 0){
                s_t = {0};
                v_t = {0};
                tmp = {0};
            }else if(popcnt_u64(h10) == 1){
                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, r, s_t, higherBitSet(h10));
                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, u, v_t, higherBitSet(h10));
            }else{
                s_t = multi_single_mult(r, s_t, h10, h11, 0);
                v_t = multi_single_mult(u, v_t, h10, h11, 0);
            }//end h10

            if (h11 == 0){
                //do nothing
            }else if(popcnt_u64(h11) == 1){
                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, s, tmp, higherBitSet(h11));
                s_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, s_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, s_t);

                left_bits_shifting(2*NUM_DIGITS_GF2X_ELEMENT, v, tmp, higherBitSet(h11));
                v_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, v_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, v_t);
            }else{
                // use r_t and u_t as temporary register to store the intermediate passage
                multi_single_mult(s, tmp, h10, h11, 16);
                s_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, s_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, s_t);

                multi_single_mult(v, tmp, h10, h11, 16);
                v_t = gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, v_t,
                                2*NUM_DIGITS_GF2X_ELEMENT, tmp,
                                2*NUM_DIGITS_GF2X_ELEMENT, v_t);
            }//end h11


            r = r_t;
            s = s_t;
            u = u_t;
            v = v_t;
        }
    }


}
