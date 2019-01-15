#define w (DIGIT_SIZE_b)

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


void matrix_mult(DIGIT a[2][2], DIGIT b[2][2]){
        DIGIT h[2][2] = {0};
        int i, j, k;

        for(i = 0; i < 2, i++){
            for(j = 0; j < 2, j++){
                for(k = 0; k < 2, k++){

                    h[i][j] += a[i][k] * b[k][j]; //gf2xadd?

                }
            }
        }
        b = h;
}


void multi_single_mult(DIGIT in[], const DIGIT matrix[], int imm){
    int l = m-2;
    __m128i h,y1,y2,y3,y4,y5;
    _m64 xr0,x1,x2;

    h = _mm_lddqu_si128((__m128i *)&matrix[0]);

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

int inverse(DIGIT out[], const DIGIT in[]){
    DIGIT v[NUM_DIGITS_GF2X_ELEMENT] = {0}, // V(x)
                u[NUM_DIGITS_GF2X_ELEMENT] = {0}, // U(x)
                    s[NUM_DIGITS_GF2X_ELEMENT] = {0}, // S(x)
                        r[NUM_DIGITS_GF2X_ELEMENT] = {0}; // R(x)

    u[NUM_DIGITS_GF2X_ELEMENT-1] = 0x1;
    v[NUM_DIGITS_GF2X_ELEMENT-1] = 0x0;


    DIGIT c, d; //C(x),D(x)
    DIGIT h[2][2]; // matrix H(x)

    int m = NUM_BITS_GF2X_ELEMENT +1 / w;
    int shift_amount = 0;
    int deg_r = NUM_BITS_GF2X_ELEMENT;
    int deg_s = NUM_BITS_GF2X_ELEMENT;

    DIGIT mask = 0x1;
    int i,j;

    for (i = NUM_DIGITS_GF2X_MODULUS-1; i >= 1 ; i--) r[i] = in[i];


    while (deg_r > 0) {
        c = r[0]; //R(m-1)
        d = s[0];

        if(c == 0){ //C(x) = 0
            __m128i y1,y2;

            for(j = 0; j<m-1; j= j+2){ // may use memcpy( dest* , source*, bytes);
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
            h[0][0] = 0x1;
            h[0][1] = 0x0;
            h[1][0] = 0x0;
            h[1][1] = 0x1;
            j = 1;

            while(j < w && deg_r > 0){
                j++;
                if(c & mask == 0){
                    c << 1;
                    DIGIT h1[2][2] = {2,0,0,1};
                    matrix_mult(h1,h);
                    deg_r --;
                }else{
                    if(deg_r == deg_s){
                        deg_r--;
                        if(d & mask == 1){
                            DIGIT tmp = c;
                            c = c - d;
                            c << 1;
                            d = tmp;
                            DIGIT h2[2][2] = {2,2,1,0};
                            matrix_mult(h2,h);
                        }else{
                            DIGIT tmp = c;
                            c = d << 1;
                            d = tmp;
                            DIGIT h2[2][2] = {0,2,1,0};
                            matrix_mult(h2,h);
                        }
                    }//endif
                    else{
                        deg_s--;
                        if(d & mask == 1){
                            d = c - d;
                            d << 1;
                            DIGIT h3[2][2] = {1,0,2,2};
                            matrix_mult(h3,h);
                        }else{
                            d << 1;
                            DIGIT h3[2][2] = {1,0,0,2};
                            matrix_mult(h3,h);
                        }
                    }
                }
            }//end while
            r_h0[NUM_DIGITS_GF2X_ELEMENT] = {0},
                r_h2[NUM_DIGITS_GF2X_ELEMENT] = {0},
                    s_h1[NUM_DIGITS_GF2X_ELEMENT] = {0},
                        s_h3[NUM_DIGITS_GF2X_ELEMENT] = {0},
                            u_h0[NUM_DIGITS_GF2X_ELEMENT] = {0},
                                u_h2[NUM_DIGITS_GF2X_ELEMENT] = {0},
                                    v_h1[NUM_DIGITS_GF2X_ELEMENT] = {0},
                                        v_h3[NUM_DIGITS_GF2X_ELEMENT] = {0};

            if(h[0][0] == 0){
                r_h0 = 0;
                u_h0 = 0;
            }
            else if(popcnt_u64(h[0][0]) == 1){ //_BitScanForward64(shift, h[i][i]) ?
                int shift;
                if(h[0][0] & mask_x3){
                    shift = 3;
                }else if(h[0][0] & mask_x2){
                    shift = 2;
                }else if(h[0][0] & mask_x){
                    shift = 1;
                }

                r_h0 = left_bits_shifting(NUM_DIGITS_GF2X_ELEMENT, r, r_h0, shift);
                u_h0 = left_bits_shifting(NUM_DIGITS_GF2X_ELEMENT, u, u_h0, shift);
            }
            else{
                r_h0 = multi_single_mult(r, h[0], 0);
                u_h0 = multi_single_mult(u, h[0], 0);
            } //end h[0][0]

            if (h[0][1] == 0){
                s_h1 = 0;
                v_h1 = 0;
            }else{
                s_h1 = multi_single_mult(s, h[0], 16);
                v_h1 = multi_single_mult(v, h[0], 16);
            }

            if (h[1][0] == 0){
                r_h2 = 0;
                u_h2 = 0;
            }else{
                r_h2 = multi_single_mult(r, h[1], 0);
                u_h2 = multi_single_mult(u, h[1], 0);
            }
            if (h[1][1] == 0){
                s_h3 = 0;
                v_h3 = 0;
            }else{
                s_h3 = multi_single_mult(s, h[1], 16);
                v_h3 = multi_single_mult(v, h[1], 16);
            }

            r = r_h0 + s_h1;//+ should be a gf2x add
            s = r_h2 + s_h3;
            u = u_h0 + v_h1;
            v = u_h2 + v_h3;
        }
    }













}
