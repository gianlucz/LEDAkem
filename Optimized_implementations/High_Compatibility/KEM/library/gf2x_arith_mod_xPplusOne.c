/**
 *
 * Optimized ISO-C11 Implementation of LEDAcrypt using GCC built-ins.
 *
 * @version 3.0 (May 2020)
 *
 * In alphabetical order:
 *
 * @author Marco Baldi <m.baldi@univpm.it>
 * @author Alessandro Barenghi <alessandro.barenghi@polimi.it>
 * @author Franco Chiaraluce <f.chiaraluce@univpm.it>
 * @author Gerardo Pelosi <gerardo.pelosi@polimi.it>
 * @author Paolo Santini <p.santini@pm.univpm.it>
 *
 * This code is hereby placed in the public domain.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS ''AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHORS OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 **/

#include "architecture_detect.h"
#include "gf2x_arith_mod_xPplusOne.h"
#include <string.h>  // memcpy(...), memset(...)
#include <stdalign.h>
#include "djbsort.h"



/*----------------------------------------------------------------------------*/

#if (defined(DIGIT_IS_UINT8) || defined(DIGIT_IS_UINT16))
static
uint8_t byte_reverse_with_less32bitDIGIT(uint8_t b)
{
   uint8_t r = b;
   int s = (sizeof(b) << 3) - 1;
   for (b >>= 1; b; b >>= 1) {
      r <<= 1;
      r |= b & 1;
      s--;
   }
   r <<= s;
   return r;
} // end byte_reverse_less32bitDIGIT
#endif

#if defined(DIGIT_IS_UINT32)
static
uint8_t byte_reverse_with_32bitDIGIT(uint8_t b)
{
   b = ( (b * 0x0802LU & 0x22110LU) | (b * 0x8020LU & 0x88440LU)
       ) * 0x10101LU >> 16;
   return b;
} // end byte_reverse_32bitDIGIT
#endif

#if defined(DIGIT_IS_UINT64)
static
uint8_t byte_reverse_with_64bitDIGIT(uint8_t b)
{
   b = (b * 0x0202020202ULL & 0x010884422010ULL) % 1023;
   return b;
} // end byte_reverse_64bitDIGIT
#endif

/*----------------------------------------------------------------------------*/

static
DIGIT reverse_digit(const DIGIT b)
{
   int i;
   union toReverse_t {
      uint8_t inByte[DIGIT_SIZE_B];
      DIGIT digitValue;
   } toReverse;

   toReverse.digitValue = b;
#if defined(DIGIT_IS_UINT64)
   for (i = 0; i < DIGIT_SIZE_B; i++) {
      toReverse.inByte[i] = byte_reverse_with_64bitDIGIT(toReverse.inByte[i]);
   }
   return __builtin_bswap64(toReverse.digitValue);
#elif defined(DIGIT_IS_UINT32)
   for (i = 0; i < DIGIT_SIZE_B; i++) {
      toReverse.inByte[i] = byte_reverse_with_32bitDIGIT(toReverse.inByte[i]);
   }
   return __builtin_bswap32(toReverse.digitValue);
#elif defined(DIGIT_IS_UINT16)
   for (i = 0; i < DIGIT_SIZE_B; i++) {
      toReverse.inByte[i] = byte_reverse_with_less32bitDIGIT(toReverse.inByte[i]);
   }
   reversed = __builtin_bswap16(toReverse.digitValue);
#elif defined(DIGIT_IS_UINT8)
   return byte_reverse_with_less32bitDIGIT(toReverse.inByte[0]);
#else
#error "Missing implementation for reverse_digit(...) \
with this CPU word bitsize !!! "
#endif
   return toReverse.digitValue;
} // end reverse_digit

/*----------------------------------------------------------------------------*/

void gf2x_transpose_in_place(DIGIT A[])
{
   /* it keeps the lsb in the same position and
    * inverts the sequence of the remaining bits
    */

   DIGIT mask = (DIGIT)0x1;
   DIGIT rev1, rev2, a00;
   int i, slack_bits_amount = NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_b - P;

   if (NUM_DIGITS_GF2X_ELEMENT == 1) {
      a00 = A[0] & mask;
      A[0] = A[0] >> 1;
      rev1 = reverse_digit(A[0]);
#if (NUM_DIGITS_GF2X_MOD_P_ELEMENT*DIGIT_SIZE_b - P)
      rev1 >>= (DIGIT_SIZE_b-(P%DIGIT_SIZE_b));
#endif
      A[0] = (rev1 & (~mask)) | a00;
      return;
   }

   a00 = A[NUM_DIGITS_GF2X_ELEMENT-1] & mask;
   right_bit_shift_n(NUM_DIGITS_GF2X_ELEMENT, A,1);

   for (i = NUM_DIGITS_GF2X_ELEMENT-1; i >= (NUM_DIGITS_GF2X_ELEMENT+1)/2; i--) {
      rev1 = reverse_digit(A[i]);
      rev2 = reverse_digit(A[NUM_DIGITS_GF2X_ELEMENT-1-i]);
      A[i] = rev2;
      A[NUM_DIGITS_GF2X_ELEMENT-1-i] = rev1;
   }
   if (NUM_DIGITS_GF2X_ELEMENT % 2 == 1) {
      A[NUM_DIGITS_GF2X_ELEMENT/2] = reverse_digit(A[NUM_DIGITS_GF2X_ELEMENT/2]);
   }

   if (slack_bits_amount) {
      right_bit_shift_n(NUM_DIGITS_GF2X_ELEMENT, A,slack_bits_amount);
   }
   A[NUM_DIGITS_GF2X_ELEMENT-1] = (A[NUM_DIGITS_GF2X_ELEMENT-1] & (~mask)) | a00;
} // end transpose_in_place

/*----------------------------------------------------------------------------*/
/* computes poly times digit multiplication as a support for KTT inverse */
/* PRE : nr = na + 1 */

#if (defined HIGH_PERFORMANCE_X86_64)
#define GF2X_DIGIT_TIMES_POLY_MUL gf2x_digit_times_poly_mul_avx
static
void gf2x_digit_times_poly_mul_avx(const int nr,
                                   DIGIT Res[NUM_DIGITS_GF2X_ELEMENT+1],
                                   const int na, const DIGIT A[],
                                   const DIGIT B)
{

   __m128i prodRes0,prodRes1,
           accumRes,loopCarriedWord,lowToHighWord,
           wideB,wideA;

   int i;
   wideB=_mm_set_epi64x(0, B);
   loopCarriedWord = _mm_set_epi64x(0,0);

   for (i = na-1; i >= 1 ; i=i-2) {
      /*wideA contains [ A[i] A[i-1] ] */
      wideA = _mm_lddqu_si128((__m128i *)&A[i-1]);

      prodRes0 = _mm_clmulepi64_si128(wideA, wideB, 1);
      prodRes1 = _mm_clmulepi64_si128(wideA, wideB, 0);

      accumRes = _mm_xor_si128(loopCarriedWord,prodRes0);
      lowToHighWord = _mm_slli_si128(prodRes1,8);
      accumRes = _mm_xor_si128(accumRes,lowToHighWord);

      accumRes = (__m128i) _mm_shuffle_pd( (__m128d) accumRes,
                                           (__m128d) accumRes, 1);
      _mm_storeu_si128((__m128i *)(&Res[i]), accumRes);

      loopCarriedWord = _mm_srli_si128(prodRes1,8);
   }
   if (i == 0) { /*skipped last iteration i=0, compensate*/
      prodRes0 = _mm_clmulepi64_si128(_mm_set_epi64x(0, A[0]), wideB, 0);

      accumRes = loopCarriedWord;
      accumRes = _mm_xor_si128(accumRes,prodRes0);
      accumRes = (__m128i) _mm_shuffle_pd( (__m128d) accumRes,
                                           (__m128d) accumRes, 1);
      _mm_storeu_si128((__m128i *)(&Res[0]), accumRes);
   } else { /*i == 1*/
      /*regular exit condition, do nothing*/
   }

}

#else
#define GF2X_DIGIT_TIMES_POLY_MUL gf2x_digit_times_poly_mul

void gf2x_digit_times_poly_mul(const int nr,
                               DIGIT Res[NUM_DIGITS_GF2X_ELEMENT+1],
                               const int na, const DIGIT A[],
                               const DIGIT B)
{

   DIGIT pres[2];
   Res[nr-1]=0;
   for (int i = (nr-1)-1; i >= 0 ; i--) {
      GF2X_MUL(2, pres, 1, &A[i], 1, &B);
      Res[i+1] = Res[i+1] ^ pres[1];
      Res[i] =  pres[0];
   }
}
#endif

/*----------------------------------------------------------------------------
*
* Based on: K. Kobayashi, N. Takagi and K. Takagi, "Fast inversion algorithm in
* GF(2m) suitable for implementation with a polynomial multiply instruction on
* GF(2)," in IET Computers & Digital Techniques, vol. 6, no. 3, pp. 180-185,
* May 2012. doi: 10.1049/iet-cdt.2010.0006
*/

int gf2x_mod_inverse_KTT1(DIGIT out[],
                         const DIGIT in[])   /* in^{-1} mod x^P-1 */
{

#if NUM_DIGITS_GF2X_MODULUS == NUM_DIGITS_GF2X_ELEMENT
   DIGIT s[NUM_DIGITS_GF2X_ELEMENT+1] = {0},
                                        r[NUM_DIGITS_GF2X_ELEMENT+1];
   r[0]=0;
   memcpy(r+1,in, NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);

   /* S starts set to the modulus */
   s[NUM_DIGITS_GF2X_ELEMENT+1-1] = 1;
   s[0+1] |= ((DIGIT)1) << MSb_POSITION_IN_MSB_DIGIT_OF_MODULUS;

   DIGIT v[2*NUM_DIGITS_GF2X_ELEMENT] = {0},
                                        u[2*NUM_DIGITS_GF2X_ELEMENT] = {0};

   u[2*NUM_DIGITS_GF2X_ELEMENT-1] = (DIGIT) 2; /* x */

   int deg_r = NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_b -1;
   int deg_s = NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_b -1;

   DIGIT c,d;
   DIGIT h00,h01,h10,h11;

   DIGIT hibitmask = ( (DIGIT) 1) << (DIGIT_SIZE_b-1);

   DIGIT r_h00[NUM_DIGITS_GF2X_ELEMENT+2];
   DIGIT s_h01[NUM_DIGITS_GF2X_ELEMENT+2];
   DIGIT r_h10[NUM_DIGITS_GF2X_ELEMENT+2];
   DIGIT s_h11[NUM_DIGITS_GF2X_ELEMENT+2];
   DIGIT u_h00[2*NUM_DIGITS_GF2X_ELEMENT+1];
   DIGIT v_h01[2*NUM_DIGITS_GF2X_ELEMENT+1];
   DIGIT u_h10[2*NUM_DIGITS_GF2X_ELEMENT+1];
   DIGIT v_h11[2*NUM_DIGITS_GF2X_ELEMENT+1];

   while(deg_r > 0) {
      c=r[1];
      d=s[1];
      if(c == 0) {
         left_DIGIT_shift_n(NUM_DIGITS_GF2X_ELEMENT+1,r,1);
         left_DIGIT_shift_n(2*NUM_DIGITS_GF2X_ELEMENT,u,1);
         deg_r = deg_r - DIGIT_SIZE_b;
      } else {
         /* H = I */
         h00 = 1;
         h01 = 0;
         h10 = 0;
         h11 = 1;
         for(int j = 1 ; (j < DIGIT_SIZE_b) && (deg_r > 0) ; j++) {
            if ( (c & hibitmask) == 0) { /* */
               c = c << 1;

               h00 = h00 << 1;
               h01 = h01 << 1;
               deg_r--;
            } else { /* hibit r[0] set */
               if (deg_r == deg_s) {
                  deg_r--;
                  if ( (d & hibitmask) == hibitmask) { /* hibit r[0],s[0] set, deg_r == deg_s */
                     DIGIT temp = c;
                     c = (c^d) << 1; /* (c-d)*x */
                     d = temp;
                     /*mult H*/
                     DIGIT r00;
                     r00 = (h00 << 1) ^ (h10 << 1);
                     DIGIT r01;
                     r01 = (h01 << 1) ^ (h11 << 1);
                     h10 = h00;
                     h11 = h01;
                     h00 = r00;
                     h01 = r01;
                  } else { /* hibit r[0] set, s[0] unset, deg_r == deg_s */
                     DIGIT temp;
                     temp = c;
                     c = d << 1;
                     d = temp;
                     /*mult H*/
                     DIGIT r00;
                     r00 = (h10 << 1);
                     DIGIT r01;
                     r01 = (h11 << 1);
                     h10 = h00;
                     h11 = h01;
                     h00 = r00;
                     h01 = r01;
                  }
               } else { /* if (deg_r != deg_s) */
                  deg_s--;
                  if ( (d & hibitmask) == hibitmask) { /* hibit r[0],s[0] set, deg_r != deg_s */
                     d = (c^d) << 1; /* (c-d) * x*/
                     /* mult H */
                     h10 = (h00 << 1) ^ (h10 << 1);
                     h11 = (h01 << 1) ^ (h11 << 1);
                  } else { /* hibit r[0] set, s[0] unset, deg_r != deg_s */
                     d = d << 1;
                     /*mul H*/

                     h10 = h10 << 1;
                     h11 = h11 << 1;
                  }
               } /*(deg_r == deg_s)*/
            } /* if ( (c & ((DIGIT 1) << (DIGIT_SIZE_b-1))) == 0) */
         } /* while */
         /*update r , s */

         GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, r_h00,
                                   NUM_DIGITS_GF2X_ELEMENT+1, r,
                                   h00);
         GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, s_h01,
                                   NUM_DIGITS_GF2X_ELEMENT+1, s,
                                   h01);
         GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, r_h10,
                                   NUM_DIGITS_GF2X_ELEMENT+1, r,
                                   h10);
         GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, s_h11,
                                   NUM_DIGITS_GF2X_ELEMENT+1, s,
                                   h11);

         gf2x_add(NUM_DIGITS_GF2X_ELEMENT+1, r,
                  NUM_DIGITS_GF2X_ELEMENT+1, r_h00+1,
                  NUM_DIGITS_GF2X_ELEMENT+1, s_h01+1);

         gf2x_add(NUM_DIGITS_GF2X_ELEMENT+1, s,
                  NUM_DIGITS_GF2X_ELEMENT+1, r_h10+1,
                  NUM_DIGITS_GF2X_ELEMENT+1, s_h11+1);

         /* *********************** update u, v *************************/
         GF2X_DIGIT_TIMES_POLY_MUL(2*NUM_DIGITS_GF2X_ELEMENT+1, u_h00,
                                   2*NUM_DIGITS_GF2X_ELEMENT, u,
                                   h00);
         GF2X_DIGIT_TIMES_POLY_MUL(2*NUM_DIGITS_GF2X_ELEMENT+1, v_h01,
                                   2*NUM_DIGITS_GF2X_ELEMENT, v,
                                   h01);
         GF2X_DIGIT_TIMES_POLY_MUL(2*NUM_DIGITS_GF2X_ELEMENT+1, u_h10,
                                   2*NUM_DIGITS_GF2X_ELEMENT, u,
                                   h10);
         GF2X_DIGIT_TIMES_POLY_MUL(2*NUM_DIGITS_GF2X_ELEMENT+1, v_h11,
                                   2*NUM_DIGITS_GF2X_ELEMENT, v,
                                   h11);

         gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, u,
                  2*NUM_DIGITS_GF2X_ELEMENT, u_h00+1,
                  2*NUM_DIGITS_GF2X_ELEMENT, v_h01+1);
         gf2x_add(2*NUM_DIGITS_GF2X_ELEMENT, v,
                  2*NUM_DIGITS_GF2X_ELEMENT, u_h10+1,
                  2*NUM_DIGITS_GF2X_ELEMENT, v_h11+1);
      }
   }
   if (deg_r == 0) {
      memcpy(out,u,NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
   } else {
      memcpy(out,v,NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
   }
#else
#error IMPLEMENT MEMCPY INTO A LARGER OPERAND
#endif

   return 0;
}


void gf2x_mod_mul(DIGIT Res[], const DIGIT A[], const DIGIT B[])
{

   DIGIT aux[2*NUM_DIGITS_GF2X_ELEMENT];
   GF2X_MUL(2*NUM_DIGITS_GF2X_ELEMENT, aux,
            NUM_DIGITS_GF2X_ELEMENT, A,
            NUM_DIGITS_GF2X_ELEMENT, B);
   gf2x_mod(Res, 2*NUM_DIGITS_GF2X_ELEMENT, aux);

} // end gf2x_mod_mul

/*----------------------------------------------------------------------------*/
/* Obtains fresh randomness and seed-expands it until all the required positions
 * for the '1's in the circulant block are obtained */

void rand_circulant_sparse_block(POSITION_T *pos_ones,
                                 const int countOnes,
                                 AES_XOF_struct *seed_expander_ctx)
{

   int duplicated, placedOnes = 0;

   while (placedOnes < countOnes) {
      int p = rand_range(NUM_BITS_GF2X_ELEMENT,
                         BITS_TO_REPRESENT(P),
                         seed_expander_ctx);
      duplicated = 0;
      for (int j = 0; j < placedOnes; j++) {
         if (pos_ones[j] == p) {
            duplicated = 1;
         }
      }
      if (duplicated == 0) {
         pos_ones[placedOnes] = p;
         placedOnes++;
      }
   }
} // rand_circulant_sparse_block

/*----------------------------------------------------------------------------*/

void rand_error_pos(POSITION_T errorPos[NUM_ERRORS_T],
                    AES_XOF_struct *seed_expander_ctx)
{

   int duplicated, counter = 0;

   while (counter < NUM_ERRORS_T) {
      int p = rand_range(N0*NUM_BITS_GF2X_ELEMENT,BITS_TO_REPRESENT(P),
                         seed_expander_ctx);
      duplicated = 0;
      for (int j = 0; j < counter; j++) {
         if (errorPos[j] == p) {
            duplicated = 1;
         }
      }
      if (duplicated == 0) {
         errorPos[counter] = p;
         counter++;
      }
   }
} // end rand_error_pos

/*----------------------------------------------------------------------------*/

void rand_error_pos_shake(POSITION_T errorPos[NUM_ERRORS_T],
                          xof_shake_t *state)
{

   int duplicated, counter = 0;

   while (counter < NUM_ERRORS_T) {
      int p = rand_range_shake(N0*NUM_BITS_GF2X_ELEMENT,BITS_TO_REPRESENT(P),
                               state);
      duplicated = 0;
      for (int j = 0; j < counter; j++) {
         if (errorPos[j] == p) {
            duplicated = 1;
         }
      }
      if (duplicated == 0) {
         errorPos[counter] = p;
         counter++;
      }
   }
} // end rand_error_pos_shake

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/
/*-----------------------------CONSTANT TIME ARITHMETIC-----------------------*/
/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

#define LO_SHIFT_AMT_BITS (BITS_TO_REPRESENT(DIGIT_SIZE_b-1))
#define HI_SHIFT_AMT_BITS (BITS_TO_REPRESENT(P) - LO_SHIFT_AMT_BITS)
/* intended as *left* *cyclic* shift, acting in-place,
 * i.e. multiply by a monomial x^shift_amt */
#if (defined HIGH_PERFORMANCE_X86_64)
#define CTIME_IF_256(mask,then,else)  _mm256_blendv_epi8(else, then, mask)
#endif
#define CTIME_SWAP(condmask,true_val,false_val) ((true_val & condmask) | (false_val & ~condmask))


#if (defined CONSTANT_TIME)
/* same as gf2x_mul_monom_inplace_CT, just acts out-of-place to ease
 * sparse2dense mul, shifted variable does not need to be clean before use*/
static inline
void word_level_shift_CT(DIGIT *restrict shifted_param,
                         POSITION_T high_shift_amt,
                         DIGIT *restrict to_shift)
{
   DIGIT current_buf[NUM_DIGITS_GF2X_ELEMENT];
   DIGIT mask;
   DIGIT *restrict shifted, * restrict current, * restrict tmp_for_ptrswap;
   shifted = shifted_param;
   current = current_buf;
   memcpy(current,to_shift,NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);

   for (int i = 0; i < HI_SHIFT_AMT_BITS; i++) {
      /* power-of-two matching current inter-word shift bit */
      int word_shift_amt = (1 << i);

      /* extract and remove high shift amount LSB */
      DIGIT lsb_of_high_shift_amt = (high_shift_amt & 1);
      high_shift_amt >>= 1;
      /* conditional mask = 0xFF..FF if current bit of inter-word shift idx is set */
      mask = 0 - lsb_of_high_shift_amt;

#if (defined HIGH_PERFORMANCE_X86_64)
      __m256i vector_mask = _mm256_set_epi64x ((DIGIT)0-lsb_of_high_shift_amt,
                            (DIGIT)0-lsb_of_high_shift_amt,
                            (DIGIT)0-lsb_of_high_shift_amt,
                            (DIGIT)0-lsb_of_high_shift_amt);
      /* condit-pull whole digits towards the MSB, starting from the
       *word_shift_amt - th  one, that is including the one which will have slack */
      {
         int j = 0;
         __m256i tmp,tmp2;
         for (; j < NUM_DIGITS_GF2X_ELEMENT-word_shift_amt-3; j = j+4) {
            tmp = _mm256_lddqu_si256 ((__m256i *) (current+j+word_shift_amt));
            tmp2 = _mm256_lddqu_si256 ((__m256i *) (current+j));
            tmp = CTIME_IF_256(vector_mask,tmp,tmp2);
            _mm256_storeu_si256(  (__m256i *) (&shifted[j]), tmp);
         }
         for (; j < NUM_DIGITS_GF2X_ELEMENT-word_shift_amt; j++) {
            shifted[j] = CTIME_SWAP(mask,current[j+word_shift_amt],current[j]);
         }
      }
#else
      /* condit-pull whole digits towards the MSB, starting from the word_shift_amt - th
       * one, that is including the one which will have slack */
      for (int j = 0; j < NUM_DIGITS_GF2X_ELEMENT-word_shift_amt; j++) {
         shifted[j] = CTIME_SWAP(mask,current[j+word_shift_amt],current[j]);
      }
#endif
      /* collect the slack carryover */
      DIGIT slack_carryover = SLACK_EXTRACT(shifted[0]);
      shifted[0] &= SLACK_CLEAR_MASK;

      /* move the remaining topmost word_shift_amt words (0th to word_shift_amt-1
       * one) taking care of tucking in the slack carryover */
#if (defined HIGH_PERFORMANCE_X86_64)
      if(word_shift_amt >=4) { /* at least enough bits to fill an AVX2 register */
         /* I have enough word material to move to gain something substantial
          * via AVX2*/
         DIGIT next_carryover;
         for (int j = word_shift_amt-4 ; j >=0 ; j = j-4) {

            __m256i in_motion = _mm256_lddqu_si256((__m256i *) (current+j));
            __m256i hi_tgt_part  = _mm256_slli_epi64(in_motion, SLACK_SIZE  );
            __m256i low_tgt_part = _mm256_srli_epi64(in_motion,(DIGIT_SIZE_b - SLACK_SIZE));

            next_carryover = _mm256_extract_epi64 (low_tgt_part, 0);
            low_tgt_part = _mm256_insert_epi64 (low_tgt_part,slack_carryover, 0);
            slack_carryover = next_carryover;
            low_tgt_part = _mm256_permute4x64_epi64 (low_tgt_part, 0x39);

            int target_idx = NUM_DIGITS_GF2X_ELEMENT-word_shift_amt+j;
            __m256i old = _mm256_lddqu_si256 ((__m256i *) (current+target_idx));
            __m256i final = CTIME_IF_256(vector_mask,_mm256_or_si256(hi_tgt_part,
                                         low_tgt_part),old);
            _mm256_storeu_si256( (__m256i *) (shifted+target_idx),final);
         }
      } else {
         for (int j = word_shift_amt-1 ; j >=0 ; j--) {
            int target_idx = NUM_DIGITS_GF2X_ELEMENT-word_shift_amt+j;
            DIGIT to_write = slack_carryover;
            to_write = to_write | (current[j] << SLACK_SIZE);
            slack_carryover = SLACK_EXTRACT(current[j]);
            shifted[target_idx] = CTIME_SWAP(mask,to_write,current[target_idx]);
         }
      }
#else
      for (int j = word_shift_amt-1 ; j >=0 ; j--) {
         int target_idx = NUM_DIGITS_GF2X_ELEMENT-1-(word_shift_amt-1)+j;
         DIGIT to_write = slack_carryover;
         to_write = to_write | (current[j] << SLACK_SIZE);
         slack_carryover = SLACK_EXTRACT(current[j]);
         shifted[target_idx] = CTIME_SWAP(mask,to_write,current[target_idx]);
      }
#endif
      tmp_for_ptrswap = current;
      current = shifted;
      shifted = tmp_for_ptrswap;
   }
   /* if the number of iterations is  even, the data is placed in the*/
   if ((HI_SHIFT_AMT_BITS) %2 ==0) {
      memcpy(shifted, current, NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
   }
}
#else
#if (defined HIGH_PERFORMANCE_X86_64)
static inline
void word_level_shift_VT(DIGIT *restrict shifted_param,
                         POSITION_T high_shift_amt,
                         DIGIT *restrict to_shift)
{

   /* condit-pull whole digits towards the MSB, starting from the
    *high_shift_amt - th  one, that is including the one which will have slack */
   {
      int j = 0;
      __m256i tmp;
      /*if there is enough material to have at least a full AVX2 reg to shift*/
      if(NUM_DIGITS_GF2X_ELEMENT-high_shift_amt >=4) {
         for (; j < NUM_DIGITS_GF2X_ELEMENT-high_shift_amt-3; j = j+4) {
            tmp = _mm256_lddqu_si256 ((__m256i *) (to_shift+j+high_shift_amt));
            _mm256_storeu_si256(  (__m256i *) (shifted_param+j), tmp);
         }
      }
      for (; j < NUM_DIGITS_GF2X_ELEMENT-high_shift_amt; j++) {
         shifted_param[j] = to_shift[j+high_shift_amt];
      }
   }
   /* collect the slack carryover */
   DIGIT slack_carryover = SLACK_EXTRACT(shifted_param[0]);
   shifted_param[0] &= SLACK_CLEAR_MASK;

   /* move the remaining topmost high_shift_amt words (0th to high_shift_amt-1
    * one) taking care of tucking in the slack carryover */
   if(high_shift_amt >=4) {
      /* I have enough word material to move to gain something substantial
       * via AVX2*/
      DIGIT next_carryover;
      int j;
      for (j = high_shift_amt-4 ; j >=0 ; j = j-4) {

         __m256i in_motion = _mm256_lddqu_si256((__m256i *) (to_shift+j));
         __m256i hi_tgt_part  = _mm256_slli_epi64(in_motion, SLACK_SIZE  );
         __m256i low_tgt_part = _mm256_srli_epi64(in_motion,(DIGIT_SIZE_b - SLACK_SIZE));

         next_carryover = _mm256_extract_epi64 (low_tgt_part, 0);
         low_tgt_part = _mm256_insert_epi64 (low_tgt_part,slack_carryover, 0);
         slack_carryover = next_carryover;
         low_tgt_part = _mm256_permute4x64_epi64 (low_tgt_part, 0x39);

         int target_idx = NUM_DIGITS_GF2X_ELEMENT-high_shift_amt+j;
         __m256i final = _mm256_or_si256(hi_tgt_part,low_tgt_part);
         _mm256_storeu_si256( (__m256i *) (shifted_param+target_idx),final);
      }

      j+=3;
      for (; j >=0 ; j--) {
         int target_idx = NUM_DIGITS_GF2X_ELEMENT-high_shift_amt+j;
         DIGIT to_write = slack_carryover;
         to_write = to_write | (to_shift[j] << SLACK_SIZE);
         slack_carryover = SLACK_EXTRACT(to_shift[j]);
         shifted_param[target_idx] = to_write;
      }
      /* handle trailing words */
   } else {
      for (int j = high_shift_amt-1 ; j >=0 ; j--) {
         int target_idx = NUM_DIGITS_GF2X_ELEMENT-high_shift_amt+j;
         DIGIT to_write = slack_carryover;
         to_write = to_write | (to_shift[j] << SLACK_SIZE);
         slack_carryover = SLACK_EXTRACT(to_shift[j]);
         shifted_param[target_idx] = to_write;
      }
   }
}
#else
static inline
void word_level_shift_VT(DIGIT *restrict shifted_param,
                         POSITION_T high_shift_amt,
                         DIGIT *restrict to_shift)
{
   /* condit-pull whole digits towards the MSB, starting from the word_shift_amt - th
    * one, that is including the one which will have slack */
   for (int j = 0; j < NUM_DIGITS_GF2X_ELEMENT-high_shift_amt; j++) {
      shifted_param[j] = to_shift[j+high_shift_amt];
   }

   /* collect the slack carryover */
   DIGIT slack_carryover = SLACK_EXTRACT(shifted_param[0]);
   shifted_param[0] &= SLACK_CLEAR_MASK;

   /* move the remaining topmost word_shift_amt words (0th to word_shift_amt-1
    * one) taking care of tucking in the slack carryover */

   for (int j = high_shift_amt-1 ; j >=0 ; j--) {
      int target_idx = NUM_DIGITS_GF2X_ELEMENT-1-(high_shift_amt-1)+j;
      DIGIT to_write = slack_carryover;
      to_write = to_write | (to_shift[j] << SLACK_SIZE);
      slack_carryover = SLACK_EXTRACT(to_shift[j]);
      shifted_param[target_idx] = to_write;
   }
}
/* end of selector between high performance and compatible*/
#endif
/* end of selector between constant and variable time */
#endif

#if (defined CONSTANT_TIME)
#define WORD_LEVEL_SHIFT word_level_shift_CT
#else
#define WORD_LEVEL_SHIFT word_level_shift_VT
#endif

void gf2x_mod_mul_monom(DIGIT shifted[],
                        POSITION_T shift_amt,
                        const DIGIT to_shift[])
{
   DIGIT mask;
   /*shift_amt is split bitwise :  |------------------shift_amt------------------|
    *                              | inter word shift amt | intra word shift amt |
    *                                  HI_SHIFT_AMT_BITS     LO_SHIFT_AMT_BITS
    */

   /* inter word shifting, done speculatively shifting the entire operand by a
    * power of two, and conditionally committing the result */
   POSITION_T high_shift_amt = shift_amt >> LO_SHIFT_AMT_BITS;
   POSITION_T low_shift_amt = shift_amt & (((POSITION_T)1 << LO_SHIFT_AMT_BITS)
                                           -1);

   WORD_LEVEL_SHIFT(shifted,high_shift_amt,(DIGIT * restrict)to_shift);

   /* cyclic shifts inside DIGITs */
   /* extract low_shift_amt MSB for cyclic shift */
   DIGIT carryover = (shifted[0] << SLACK_SIZE) | (shifted[1] >>
                     (DIGIT_SIZE_b -SLACK_SIZE));
   carryover = carryover >> (DIGIT_SIZE_b - low_shift_amt);

   /* pure shift, carried over from left_bit_shift_n*/
   mask = ~(( (DIGIT)1 << (DIGIT_SIZE_b - low_shift_amt) ) - 1);
   /* must deal with C99 UB when shifting by variable size*/
   DIGIT zeroshift_mask = (DIGIT)0 - (!!(low_shift_amt));

#if (defined HIGH_PERFORMANCE_X86_64)
   {
      int j;
      __m256i a,b;
      for(j = 0 ; j < NUM_DIGITS_GF2X_ELEMENT-4; j = j+4) {
         a = _mm256_lddqu_si256( (__m256i *) &shifted[0] +
                                 j/4);  //load from in[j] to in[j+3]
         b = _mm256_lddqu_si256( (__m256i *) &shifted[1] +
                                 j/4);  //load from in[j+1] to in[j+4]
         a = _mm256_slli_epi64(a, low_shift_amt);
         b = _mm256_srli_epi64(b, (DIGIT_SIZE_b-low_shift_amt));
         /* no need to zeromask, the srli behavior is well defined for amount > 63 */
         _mm256_storeu_si256( (__m256i *) &shifted[0] + j/4, _mm256_or_si256(a,b));
      }
      for (; j < NUM_DIGITS_GF2X_ELEMENT-1 ; j++) {
         shifted[j] = (shifted[j] << low_shift_amt) |
                      ( zeroshift_mask & (shifted[j+1] & mask) >> (DIGIT_SIZE_b - low_shift_amt) );
      }
   }
#else
   for (int j = 0 ; j < NUM_DIGITS_GF2X_ELEMENT-1 ; j++) {
      shifted[j] = (shifted[j] << low_shift_amt) | ( zeroshift_mask &
                   (shifted[j+1] & mask) >> (DIGIT_SIZE_b - low_shift_amt) );
   }
#endif
   shifted[NUM_DIGITS_GF2X_ELEMENT-1] = (shifted[NUM_DIGITS_GF2X_ELEMENT-1] <<
                                         low_shift_amt);
   shifted[NUM_DIGITS_GF2X_ELEMENT-1] |=(zeroshift_mask & carryover);
   shifted[0] &= SLACK_CLEAR_MASK;
}

void gf2x_mod_fmac(DIGIT result[],
                   POSITION_T shift_amt,
                   const DIGIT to_shift[])
{
   DIGIT shifted_temp[NUM_DIGITS_GF2X_ELEMENT] = {0};

   DIGIT mask;
   /*shift_amt is split bitwise :  |------------------shift_amt------------------|
    *                              | inter word shift amt | intra word shift amt |
    *                                  HI_SHIFT_AMT_BITS     LO_SHIFT_AMT_BITS
    */

   /* inter word shifting, done speculatively shifting the entire operand by a
    * power of two, and conditionally committing the result */
   POSITION_T high_shift_amt = shift_amt >> LO_SHIFT_AMT_BITS;
   POSITION_T low_shift_amt = shift_amt & (((POSITION_T)1 << LO_SHIFT_AMT_BITS)
                                           -1);

   WORD_LEVEL_SHIFT(shifted_temp,high_shift_amt,(DIGIT * restrict)to_shift);

   /* cyclic shifts inside DIGITs */
   /* extract low_shift_amt MSB for cyclic shift */
   DIGIT carryover = (shifted_temp[0] << SLACK_SIZE) | (shifted_temp[1] >>
                     (DIGIT_SIZE_b -SLACK_SIZE));
   carryover = carryover >> (DIGIT_SIZE_b - low_shift_amt);

   /* pure shift, carried over from left_bit_shift_n*/
   mask = ~(( (DIGIT)1 << (DIGIT_SIZE_b - low_shift_amt) ) - 1);
   /* must deal with C99 UB when shifting by variable size*/
   DIGIT zeroshift_mask = (DIGIT)0 - (!!(low_shift_amt));

#if (defined HIGH_PERFORMANCE_X86_64)
   {
      int j;
      __m256i a,b,accu;
      for(j = 0 ; j < NUM_DIGITS_GF2X_ELEMENT-4; j = j+4) {
         a = _mm256_lddqu_si256( (__m256i *) &shifted_temp[0] +
                                 j/4); //load from in[j] to in[j+3]
         b = _mm256_lddqu_si256( (__m256i *) &shifted_temp[1] +
                                 j/4); //load from in[j+1] to in[j+4]
         accu = _mm256_lddqu_si256( (__m256i *) &result[0] + j/4);
         a = _mm256_slli_epi64(a, low_shift_amt);
         b = _mm256_srli_epi64(b, (DIGIT_SIZE_b-low_shift_amt));
         /* no need to zeromask, the srli behavior is well defined for amount > 63 */
         _mm256_storeu_si256( (__m256i *) &result[0] + j/4,
                              _mm256_xor_si256(_mm256_or_si256(a,b),accu) );
      }
      for (; j < NUM_DIGITS_GF2X_ELEMENT-1 ; j++) {
         result[j] ^= (shifted_temp[j] << low_shift_amt) | ( zeroshift_mask &
                      (shifted_temp[j+1] & mask) >> (DIGIT_SIZE_b - low_shift_amt) );
      }
   }
#else
   for (int j = 0 ; j < NUM_DIGITS_GF2X_ELEMENT-1 ; j++) {
      result[j] ^= (shifted_temp[j] << low_shift_amt) | ( zeroshift_mask &
                   (shifted_temp[j+1] & mask) >> (DIGIT_SIZE_b - low_shift_amt) );
   }
#endif
   result[NUM_DIGITS_GF2X_ELEMENT-1] ^= (shifted_temp[NUM_DIGITS_GF2X_ELEMENT-1] <<
                                         low_shift_amt) | (zeroshift_mask & carryover);
   result[0] &= SLACK_CLEAR_MASK;
}

/**********************************************************************************
   MONOMIAL MULTIPLICATION DERIVATIVES: MUL DENSE TO SPARSE AND LIFTED MUL D2S
 **********************************************************************************/

/* computes a sparse to dense multiplication using gf2x_mod_mul_monom */
void gf2x_mod_mul_dense_to_sparse(DIGIT Res[],
                                  const DIGIT dense[],
                                  const POSITION_T sparse[],
                                  unsigned int nPos)
{

   memset(Res,0,NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
   for(int i = 0; i < nPos; i++) {
      gf2x_mod_fmac(Res,sparse[i],dense);
   }
}


/**********************************************************************************
   BERNSTEIN inversion
 **********************************************************************************/
 void gf2x_scalarprod(int nr, DIGIT Res[],
                      int na, DIGIT a0[], DIGIT a1[],
                      int nb, DIGIT b0[], DIGIT b1[]
                      )
 {

     if(na == nb){
        DIGIT tmp[nr];
        GF2X_MUL(nr,Res, na,a0, nb,b0);
        GF2X_MUL(nr,tmp, na,a1, nb,b1);
        gf2x_add(nr, Res, nr, tmp, nr, Res);
     } else if (na > nb){
         DIGIT   tmp[na*2];

         DIGIT  bufb[na];
         memset(bufb,0x00,(na-nb)*DIGIT_SIZE_B);
         memcpy(bufb+(na-nb),b0,nb*DIGIT_SIZE_B);
         GF2X_MUL(na*2,tmp, na,a0, na,bufb);

         DIGIT  tmp2[na*2];

         memset(bufb,0x00,(na-nb)*DIGIT_SIZE_B);
         memcpy(bufb+(na-nb),b1,nb*DIGIT_SIZE_B);

         GF2X_MUL(na*2,tmp2, na,a1, na,bufb);
         gf2x_add(na*2, tmp2, na*2, tmp, na*2, tmp2);

         memcpy(Res,tmp2+(na-nb),nr*DIGIT_SIZE_B);
     } else /*nb > na*/ {
         DIGIT   tmp[nb*2];

         DIGIT  bufa[nb];
         memset(bufa,0x00,(nb-na)*DIGIT_SIZE_B);
         memcpy(bufa+(nb-na),a0,na*DIGIT_SIZE_B);
         GF2X_MUL(nb*2,tmp, nb, bufa, nb,b0);

         DIGIT  tmp2[nb*2];

         memset(bufa,0x00,(nb-na)*DIGIT_SIZE_B);
         memcpy(bufa+(nb-na),a1,na*DIGIT_SIZE_B);

         GF2X_MUL(nb*2,tmp2, nb,bufa, nb,b1);

         gf2x_add(nb*2, tmp2, nb*2, tmp, nb*2, tmp2);
         memcpy(Res,tmp2+(nb*2-(nb+na)),(na+nb)*DIGIT_SIZE_B);
     }
 }

 #if (defined HIGH_COMPATIBILITY_X86_64)
 static inline
 __m128i right_shift_128(__m128i in){

     __m128i a,b;
     a = _mm_srli_epi64(in,1);
     b = _mm_slli_epi64(in,DIGIT_SIZE_b-1);

     //set the high part of b = 0
     b = _mm_unpacklo_epi64( _mm_setzero_si128(),b ); //o _mm_unpacklo_epi64???
     a = _mm_or_si128(a,b);

     return a;
 }
 #endif

 #if (defined HIGH_PERFORMANCE_X86_64)
 static inline
 __m256i right_shift_256(__m256i in){

     __m256i a,b,c;
     a = _mm256_srli_epi64(in,1);

     b = _mm256_slli_epi64(in,DIGIT_SIZE_b-1);

     c = _mm256_permute4x64_epi64(b,0x93);
     c = _mm256_insert_epi64(c, (DIGIT) 0, 0);

     a = _mm256_or_si256(a,c);

     return a;
 }
 #endif

 void gf2x_reflect_in_place(DIGIT A[])
 {
    DIGIT rev1,rev2;
    for (int i = NUM_DIGITS_GF2X_ELEMENT-1; i >= (NUM_DIGITS_GF2X_ELEMENT+1)/2; i--) {
       rev1 = reverse_digit(A[i]);
       rev2 = reverse_digit(A[NUM_DIGITS_GF2X_ELEMENT-1-i]);
       A[i] = rev2;
       A[NUM_DIGITS_GF2X_ELEMENT-1-i] = rev1;
    }
    if (NUM_DIGITS_GF2X_ELEMENT % 2 == 1)
       A[NUM_DIGITS_GF2X_ELEMENT/2] = reverse_digit(A[NUM_DIGITS_GF2X_ELEMENT/2]);
 } // end transpose_in_place
 /*************************************************************************/

 #define CTIME_IF(mask,then,else)  ((mask&(then)) | (~mask&(else) ))

 #define SIGNED_DIGIT int64_t
 int divstepsx(int n, int t,
               int delta,
               DIGIT f64, DIGIT g64,
               DIGIT * p00, DIGIT * p01,
               DIGIT * p10, DIGIT * p11) {
     DIGIT u, v, q, r;
     SIGNED_DIGIT g0, f0;

     u = ((DIGIT) 1) << n;
     v = 0;
     q = 0;
     r = ((DIGIT) 1) << n;
     DIGIT tmp,tmp2;

     while (n > 0) {
       SIGNED_DIGIT swap_mask = ((delta > 0) & ((g64 & 1) != 0));
       swap_mask = (swap_mask << (DIGIT_SIZE_b-1)) >> (DIGIT_SIZE_b-1);
       delta = CTIME_IF(swap_mask,-delta,delta);
       tmp  = CTIME_IF(swap_mask,g64,f64);
       tmp2 = CTIME_IF(swap_mask,f64,g64);
       f64  = tmp;
       g64  = tmp2;

       tmp  = CTIME_IF(swap_mask,q,u);
       tmp2 = CTIME_IF(swap_mask,u,q);
       u  = tmp;
       q  = tmp2;

       tmp  = CTIME_IF(swap_mask,r,v);
       tmp2 = CTIME_IF(swap_mask,v,r);
       v  = tmp;
       r  = tmp2;

       delta++;
       g0 = (((SIGNED_DIGIT) (g64 & (DIGIT) 0x1)) << (DIGIT_SIZE_b - 1)) >>
           (DIGIT_SIZE_b - 1);

       f0 = (((SIGNED_DIGIT) (f64 & (DIGIT) 0x1)) << (DIGIT_SIZE_b - 1)) >>
           (DIGIT_SIZE_b - 1);
 //          printf(" f0000 : %lx\n", (f64 & (DIGIT) 0x1) );
 //    printf(" g0 : %lx\n", g0 );
 //    printf(" f0 : %lx\n", f0 );
       q =   (f0 & q) ^ (g0 & u);
       r =   (f0 & r) ^ (g0 & v);
       g64 = (f0 & g64) ^ (g0 & f64);
       g64 >>= 1;
       q >>= 1;
       r >>= 1;
       n--;
       t--;


    } //end while
     *p00 = u;
     *p01 = v;
     *p10 = q;
     *p11 = r;

     return delta;
 }

 #if (defined HIGH_COMPATIBILITY_X86_64)

 #define CTIME_IF_128(mask,then,else)  _mm_or_si128(_mm_and_si128(mask, then) ,_mm_andnot_si128(mask, else))
 int divstepsx_128(int n, int t,
               int delta,
               DIGIT f[], DIGIT g[],
               DIGIT * p00, DIGIT * p01,
               DIGIT * p10, DIGIT * p11) {

     if(n<64){
         return delta = divstepsx (n,n,delta,
                                 f[0],
                                 g[0],
                                 p00, p01,
                                 p10, p11);
     }
     __m128i g0, f0, g128, f128;
     __m128i one_128 = _mm_set_epi64x((DIGIT) 1, (DIGIT) 0);
     __m128i mask_128 = _mm_set_epi64x((DIGIT) 1, (DIGIT) 1);
     __m128i zero_128 = _mm_setzero_si128();

     __m128i u, v, q, r;

     g128 = _mm_lddqu_si128((__m128i *)g);
     f128 = _mm_lddqu_si128((__m128i *)f);

     DIGIT  temp = ((DIGIT) 1)<< (n-64);
     u = _mm_set_epi64x( (DIGIT) 0, temp);
     r = _mm_set_epi64x( (DIGIT) 0, temp);
     v = _mm_setzero_si128();
     q = _mm_setzero_si128();

     __m128i delta_128 = _mm_set_epi64x((SIGNED_DIGIT) delta,(SIGNED_DIGIT) delta);

     __m128i tmp,tmp2;

     while (n > 0) {
      __m128i delta_mask = _mm_cmpgt_epi64(delta_128, zero_128);

      //something like [xxx....xxx | FFF....FFF] where x is the actual mask
      __m128i g128_mask = _mm_cmpeq_epi64(_mm_and_si128(g128, one_128), one_128);

      __m128i swap_mask = _mm_and_si128(delta_mask, (__m128i)_mm_shuffle_pd((__m128d) g128_mask, (__m128d) g128_mask, 3));


       delta_128 = _mm_add_epi64(_mm_xor_si128(delta_128, swap_mask), _mm_and_si128(mask_128, swap_mask));

      // delta = CTIME_IF(swap,-delta,delta);
       tmp  = CTIME_IF_128(swap_mask,g128,f128);
       tmp2 = CTIME_IF_128(swap_mask,f128,g128);


       f128  = tmp;
       g128  = tmp2;

       tmp  = CTIME_IF_128(swap_mask,q,u);
       tmp2 = CTIME_IF_128(swap_mask,u,q);


       u  = tmp;
       q  = tmp2;

       tmp  = CTIME_IF_128(swap_mask,r,v);
       tmp2 = CTIME_IF_128(swap_mask,v,r);

       v  = tmp;
       r  = tmp2;

       //delta++;
       delta_128 = _mm_add_epi64(delta_128, mask_128);

       g0 = _mm_cmpeq_epi64(_mm_and_si128(g128, one_128), one_128);
       g0 = (__m128i)_mm_shuffle_pd((__m128d) g0, (__m128d) g0, 3);

       f0 = _mm_cmpeq_epi64(_mm_and_si128(f128, one_128), one_128);
       f0 = (__m128i)_mm_shuffle_pd((__m128d) f0, (__m128d) f0, 3);

       q =   _mm_xor_si128(_mm_and_si128(f0,q), _mm_and_si128(g0,u)); //(f0 & q) ^ (g0 & u);
       r =   _mm_xor_si128(_mm_and_si128(f0,r), _mm_and_si128(g0,v)); //(f0 & r) ^ (g0 & v);
       g128 = _mm_xor_si128(_mm_and_si128(f0,g128), _mm_and_si128(g0,f128)); //(f0 & g64) ^ (g0 & f64);

       g128 = right_shift_128(g128);
       q = right_shift_128(q);
       r = right_shift_128(r);
       n--;
       t--;
    } //end while

     _mm_storeu_si128((__m128i *) p00, u);
     _mm_storeu_si128((__m128i *) p01, v);
     _mm_storeu_si128((__m128i *) p10, q);
     _mm_storeu_si128((__m128i *) p11, r);

     return _mm_cvtsi128_si64x(delta_128);//_mm_extract_epi64(delta_128,1);
 }
 #endif

 #if (defined HIGH_PERFORMANCE_X86_64)

 #define CTIME_IF_256(mask,then,else)  _mm256_blendv_epi8(else, then, mask)
 int divstepsx_256(int n, int t,
               int delta,
               DIGIT f[], DIGIT g[],
               DIGIT * p00, DIGIT * p01,
               DIGIT * p10, DIGIT * p11)
 {
     if(n<128){
         return delta = divstepsx_128 (n,n,delta,
                                 f,
                                 g,
                                 p00, p01,
                                 p10, p11);
     }
     __m256i g0, f0, g256, f256;
     __m256i one_256 = _mm256_set_epi64x((DIGIT) 1, (DIGIT) 0,(DIGIT) 0, (DIGIT) 0);
     __m256i mask_256 = _mm256_set_epi64x((DIGIT) 1, (DIGIT) 1,(DIGIT) 1, (DIGIT) 1);
     __m256i zero_256 = _mm256_setzero_si256();


     __m256i u, v, q, r;

     g256 = _mm256_lddqu_si256((__m256i *)g);
     f256 = _mm256_lddqu_si256((__m256i *)f);

     DIGIT  temp = ((DIGIT) 1)<< (n-192);
     u = _mm256_set_epi64x( (DIGIT) 0, (DIGIT) 0, (DIGIT) 0, temp);
     r = _mm256_set_epi64x( (DIGIT) 0, (DIGIT) 0, (DIGIT) 0, temp);
     v = _mm256_setzero_si256();
     q = _mm256_setzero_si256();

     __m256i delta_256 = _mm256_set_epi64x((SIGNED_DIGIT) delta,(SIGNED_DIGIT) delta, (SIGNED_DIGIT) delta,(SIGNED_DIGIT) delta);

     __m256i tmp,tmp2;

     while (n > 0) {
      __m256i delta_mask = _mm256_cmpgt_epi64(delta_256, zero_256);

      //something like [ xx...xx | FF...FF | FF...FF | FF...FF ]   where x is the actual mask
      __m256i g256_mask = _mm256_cmpeq_epi64(_mm256_and_si256(g256, one_256), one_256);

      __m256i swap_mask = _mm256_and_si256(delta_mask, _mm256_permute4x64_epi64(g256_mask, 0xFF));


      //need to add 1 when changing sign with the xor
       delta_256 = _mm256_add_epi64(_mm256_xor_si256(delta_256, swap_mask), _mm256_and_si256(mask_256, swap_mask));
       tmp  = CTIME_IF_256(swap_mask,g256,f256);
       tmp2 = CTIME_IF_256(swap_mask,f256,g256);

       f256  = tmp;
       g256  = tmp2;

       tmp  = CTIME_IF_256(swap_mask,q,u);
       tmp2 = CTIME_IF_256(swap_mask,u,q);


       u  = tmp;
       q  = tmp2;

       tmp  = CTIME_IF_256(swap_mask,r,v);
       tmp2 = CTIME_IF_256(swap_mask,v,r);

       v  = tmp;
       r  = tmp2;

       delta_256 = _mm256_add_epi64(delta_256, mask_256);
 //      print_pol((DIGIT *)&g128,"g128",2);
 //      print_pol((DIGIT *)&f128,"f128",2);

       __m256i maskgf_tmp = _mm256_cmpeq_epi64(_mm256_and_si256(g256, one_256), one_256);
       g0 = _mm256_permute4x64_epi64(maskgf_tmp, 0xFF);

       maskgf_tmp = _mm256_cmpeq_epi64(_mm256_and_si256(f256, one_256), one_256);
       f0 = _mm256_permute4x64_epi64(maskgf_tmp, 0xFF);

 //print_pol128(q,"q");
 //print_pol128(r,"r");
       q =   _mm256_xor_si256(_mm256_and_si256(f0,q), _mm256_and_si256(g0,u));
       r =   _mm256_xor_si256(_mm256_and_si256(f0,r), _mm256_and_si256(g0,v));
       g256 = _mm256_xor_si256(_mm256_and_si256(f0,g256), _mm256_and_si256(g0,f256));


 //print_pol128(q,"q");
 //print_pol128(r,"r");


       g256 = right_shift_256(g256);
       q = right_shift_256(q);
       r = right_shift_256(r);
       n--;
       t--;

    } //end while

     _mm256_storeu_si256((__m256i *) p00, u);
     _mm256_storeu_si256((__m256i *) p01, v);
     _mm256_storeu_si256((__m256i *) p10, q);
     _mm256_storeu_si256((__m256i *) p11, r);

     return _mm256_extract_epi64(delta_256, 0);
 }
 #endif

 #if (defined HIGH_PERFORMANCE_X86_64)

 /*needed when n>128 & n<256*/
 int support_jumpdivstep(int n, int t, int delta,
                         int nf, DIGIT   f[], DIGIT g[],
                         DIGIT t00[], DIGIT t01[],
                         DIGIT t10[], DIGIT t11[])
 {
 //    printf("eccomi\n" );
         if (n < 128) {

             return delta = divstepsx_128(n, t, delta,
                             f,
                             g,
                             t00, t01,
                             t10, t11);

         }

    /* round the cutting point to a digit limit */
    int j = n*0.5;
    j = (j+128-2)/(128-1);
    j = j * (128-1);

    int num_digits_j       = (j/DIGIT_SIZE_b)+1; /* (j+DIGIT_SIZE_b-1)/DIGIT_SIZE_b */

    DIGIT p_00[num_digits_j],p_01[num_digits_j],
          p_10[num_digits_j],p_11[num_digits_j];


 //printf("delta1 = %i\n", delta);

    delta = support_jumpdivstep(j, j, delta, num_digits_j,
                        f+(nf-num_digits_j),
                        g+(nf-num_digits_j),
                        p_00, p_01, p_10, p_11);

        /* note: entire f and g must be matrixmultiplied! use the ones from above */
    DIGIT f_sum[num_digits_j+nf];
    DIGIT g_sum[num_digits_j+nf];

    gf2x_scalarprod(num_digits_j+nf, f_sum,
                    num_digits_j,    p_00, p_01,
                    nf,                    f, g);

    gf2x_scalarprod(num_digits_j+nf, g_sum,
                    num_digits_j,    p_10, p_11,
                    nf,                    f, g);
     //print_pol( g_sum, "g_sum =", num_digits_j+nf);


    right_bit_shift_wide_n(num_digits_j+nf, f_sum, j);
    right_bit_shift_wide_n(num_digits_j+nf, g_sum, j);

    /* truncate to n-j degree, i.e. to n-j bits from the bottom */
    int num_digits_nminusj = (n-j)/DIGIT_SIZE_b+1;

    DIGIT  q_00[num_digits_nminusj],
           q_01[num_digits_nminusj],
           q_10[num_digits_nminusj],
           q_11[num_digits_nminusj];

    delta = support_jumpdivstep(n - j, n - j, delta,
                        num_digits_nminusj,
                        f_sum + (num_digits_j+nf - num_digits_nminusj),
                        g_sum + (num_digits_j+nf - num_digits_nminusj),
                        q_00, q_01, q_10, q_11);

    DIGIT large_tmp[num_digits_j+num_digits_nminusj];
 //   memset(large_tmp,0x00,(num_digits_j+num_digits_nminusj)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_00, p_10,
                    num_digits_nminusj,                    q_00, q_01);
    memcpy(t00,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_01, p_11,
                    num_digits_nminusj,                    q_00, q_01);
    memcpy(t01,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_00, p_10,
                    num_digits_nminusj,                    q_10, q_11);
    memcpy(t10,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_01, p_11,
                    num_digits_nminusj,                    q_10, q_11);
    memcpy(t11,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);

    return delta;
 }
 #endif

 int jumpdivstep(int n, int t, int delta,
                 int nf, DIGIT   f[], DIGIT g[],
                 DIGIT t00[], DIGIT t01[],
                 DIGIT t10[], DIGIT t11[])
 {

 #if (defined HIGH_PERFORMANCE_X86_64)
     if (n < 256) {
         if(n < 192){
             return delta = support_jumpdivstep(n,t, delta,
                                                 nf, f, g,
                                                 t00, t01,
                                                 t10, t11);
         }
         return delta = divstepsx_256(n, t, delta,
                         f,
                         g,
                         t00, t01,
                         t10, t11);
     }
     int ws = 256;


 #elif (defined HIGH_COMPATIBILITY_X86_64)
     if (n < 128) {

         return delta = divstepsx_128(n, t, delta,
                             f,
                             g,
                             t00, t01,
                             t10, t11);
     }
     int ws = 128;
 #else

     if (n <= 63) {
      return delta = divstepsx(n, t, delta,
             f[0],
             g[0],
             t00, t01,
             t10, t11);
     }
     int ws = DIGIT_SIZE_b;
 #endif

    /* round the cutting point to a digit limit */
    int j = n*0.5;
    j = (j+ws-2)/(ws-1);
    j = j * (ws-1);

    int num_digits_j       = j/DIGIT_SIZE_b+1; /* (j+DIGIT_SIZE_b-1)/DIGIT_SIZE_b */;
    DIGIT p_00[num_digits_j],p_01[num_digits_j],
          p_10[num_digits_j],p_11[num_digits_j];


    delta = jumpdivstep(j, j, delta, num_digits_j,
                         f+(nf-num_digits_j),
                         g+(nf-num_digits_j),
                         p_00, p_01, p_10, p_11);


    /* note: entire f and g must be matrixmultiplied! use the ones from above */
    DIGIT f_sum[num_digits_j+nf];
    DIGIT g_sum[num_digits_j+nf];

    gf2x_scalarprod(num_digits_j+nf, f_sum,
                    num_digits_j,    p_00, p_01,
                    nf,                    f, g);

    gf2x_scalarprod(num_digits_j+nf, g_sum,
                    num_digits_j,    p_10, p_11,
                    nf,                    f, g);


    right_bit_shift_wide_n(num_digits_j+nf, f_sum, j);
    right_bit_shift_wide_n(num_digits_j+nf, g_sum, j);

    /* truncate to n-j degree, i.e. to n-j bits from the bottom */
    int num_digits_nminusj = (n-j)/DIGIT_SIZE_b+1;

    DIGIT  q_00[num_digits_nminusj],
           q_01[num_digits_nminusj],
           q_10[num_digits_nminusj],
           q_11[num_digits_nminusj];
  /*  memset(q_00,0x00,num_digits_nminusj*DIGIT_SIZE_B);
    memset(q_01,0x00,num_digits_nminusj*DIGIT_SIZE_B);
    memset(q_10,0x00,num_digits_nminusj*DIGIT_SIZE_B);
    memset(q_11,0x00,num_digits_nminusj*DIGIT_SIZE_B);
 */
    delta = jumpdivstep(n - j, n - j, delta,
                        num_digits_nminusj,
                        f_sum + (num_digits_j+nf - num_digits_nminusj),
                        g_sum + (num_digits_j+nf - num_digits_nminusj),
                        q_00, q_01, q_10, q_11);

    DIGIT large_tmp[num_digits_j+num_digits_nminusj];
 //   memset(large_tmp,0x00,(num_digits_j+num_digits_nminusj)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_00, p_10,
                    num_digits_nminusj,                    q_00, q_01);
    memcpy(t00,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_01, p_11,
                    num_digits_nminusj,                    q_00, q_01);
    memcpy(t01,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_00, p_10,
                    num_digits_nminusj,                    q_10, q_11);
    memcpy(t10,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);

    gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                    num_digits_j,                    p_01, p_11,
                    num_digits_nminusj,                    q_10, q_11);
    memcpy(t11,
           large_tmp+(num_digits_j+num_digits_nminusj-nf),
           (nf)*DIGIT_SIZE_B);
    return delta;
 }


 #define MATRIX_ELEM_DIGITS (((2 * P - 1)/DIGIT_SIZE_b+1)/2)+4// NUM_DIGITS_GF2X_ELEMENT+2
 int gf2x_mod_inverse_BY(DIGIT out[], const DIGIT in[])
 {
 #if NUM_DIGITS_GF2X_MODULUS == NUM_DIGITS_GF2X_ELEMENT
     DIGIT f[NUM_DIGITS_GF2X_ELEMENT] = { 0 },   // S(x)
     g[NUM_DIGITS_GF2X_ELEMENT] = { 0 };   // R(x)

     DIGIT u[MATRIX_ELEM_DIGITS] = { 0 },
           v[MATRIX_ELEM_DIGITS] = { 0 },
           q[MATRIX_ELEM_DIGITS] = { 0 },
           r[MATRIX_ELEM_DIGITS] = { 0 };

     int delta = 1;

     memcpy(g, in, NUM_DIGITS_GF2X_ELEMENT * DIGIT_SIZE_B);

     f[0] |= (((DIGIT) 0x1) << MSb_POSITION_IN_MSB_DIGIT_OF_MODULUS);
     f[NUM_DIGITS_GF2X_ELEMENT - 1] = 0x1;

     int slack_bits_amount = (DIGIT_SIZE_b * NUM_DIGITS_GF2X_ELEMENT) - P;

     gf2x_reflect_in_place(f);
     right_bit_shift_n(NUM_DIGITS_GF2X_ELEMENT, f, slack_bits_amount - 1);
     gf2x_reflect_in_place(g);
     right_bit_shift_n(NUM_DIGITS_GF2X_ELEMENT, g, slack_bits_amount);

     DIGIT largef[MATRIX_ELEM_DIGITS], largeg[MATRIX_ELEM_DIGITS];
     memset(largef,0x00,MATRIX_ELEM_DIGITS*DIGIT_SIZE_B);
     memcpy(largef+(MATRIX_ELEM_DIGITS-NUM_DIGITS_GF2X_ELEMENT),
            f,
            NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
     memset(largeg,0x00,MATRIX_ELEM_DIGITS*DIGIT_SIZE_B);
     memcpy(largeg+(MATRIX_ELEM_DIGITS-NUM_DIGITS_GF2X_ELEMENT),
            g,
            NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);

     delta = jumpdivstep(2 * P - 1, 2 * P - 1,
                         delta, MATRIX_ELEM_DIGITS,
                         largef, largeg, u, v, q, r);

     //print_pol(v,"v",MATRIX_ELEM_DIGITS);

     /* Since I should reverse d-1 I can just reverse on d after dividing by x
        return kx( x^(2*d-2)*P[0][1] /f[0]).reverse(d-1) */
     right_bit_shift_n(MATRIX_ELEM_DIGITS, v, 1);

     gf2x_reflect_in_place(v + (MATRIX_ELEM_DIGITS - NUM_DIGITS_GF2X_ELEMENT));

     /* reflection is full-word-wise, shift away the slack bits */
     right_bit_shift_n(NUM_DIGITS_GF2X_ELEMENT, v + (MATRIX_ELEM_DIGITS - NUM_DIGITS_GF2X_ELEMENT), slack_bits_amount);

     memcpy(out, v + (MATRIX_ELEM_DIGITS - NUM_DIGITS_GF2X_ELEMENT),
       NUM_DIGITS_GF2X_ELEMENT * DIGIT_SIZE_B);

     DIGIT clear_slack_mask = ( ((DIGIT) 1) <<
                                ((DIGIT_SIZE_b) - slack_bits_amount) ) - 1;
     out[0] = out[0] & clear_slack_mask;

 #else
 #error IMPLEMENT MEMCPY INTO A LARGER OPERAND
 #endif
     return 0;
 }
