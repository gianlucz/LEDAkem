/*----------------------------------------------------------------------------
 *
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
 *
 *----------------------------------------------------------------------------*/
#include <inttypes.h>
#include <limits.h>
#include <stddef.h>
#include <stdio.h>
#include <stdalign.h>
#include <alloca.h>
#include "gf2x_limbs.h"
#include "gf2x_arith_mod_xPplusOne.h"
#include "architecture_detect.h"
#include "timing_and_stats.h"

//#define P 367//5101//92669//89521//78893//72019//68483//58057//48029//45823//41161//38039//28393//20183//14939//10009//
#define NUM_BITS_GF2X_ELEMENT (P)    // modulus(x) = x^P-1
#define M (((P + 1)/DIGIT_SIZE_b)+1)
#define NUM_DIGITS_GF2X_ELEMENT ((P+DIGIT_SIZE_b-1)/DIGIT_SIZE_b)
#define MSb_POSITION_IN_MSB_DIGIT_OF_MODULUS (P-DIGIT_SIZE_b*(NUM_DIGITS_GF2X_MODULUS-1))

#include <string.h>
#include <assert.h>

void print_pol(DIGIT pol[], char polin[], int len)
{
    int i;
    fprintf(stderr,"%s", polin);
    for (i = 0; i < len; i++) {
    fprintf(stderr," %016lX ", pol[i]);
    }
    fprintf(stderr,"\n");


}

void print_pol128(__m128i pol, char polin[])
{

    printf("%s: ", polin);
    printf("hi: %llx || ", _mm_extract_epi64(pol, 1));
    printf("lo: %llx ", _mm_extract_epi64(pol, 0));

    printf("\n");
}

void print_pol256(__m256i pol, char polin[])
{
    DIGIT a,b,c,d;
    a = _mm256_extract_epi64(pol,3);
    b = _mm256_extract_epi64(pol,2);
    c = _mm256_extract_epi64(pol,1);
    d = _mm256_extract_epi64(pol,0);
    printf("%s: ", polin);
    printf("%lx || %lx || %lx || %lx ", a,b,c,d);
    printf("\n");
}

/*----------------------------------------------------------------------------*/
/* computes modular inverse according to the Kobayashi Takahagi^2 digitwise method */

int gf2x_mod_inverse_KTT(DIGIT out[], const DIGIT in[]){  /* in^{-1} mod x^P-1 */

#if NUM_DIGITS_GF2X_MODULUS == NUM_DIGITS_GF2X_ELEMENT
 DIGIT s[NUM_DIGITS_GF2X_ELEMENT+1] = {0},
       r[NUM_DIGITS_GF2X_ELEMENT+1];
 r[0]=0;
 memcpy(r+1,in, NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);

 /* S starts set to the modulus */
 s[NUM_DIGITS_GF2X_ELEMENT+1-1] = 1;
 s[0+1] |= ((DIGIT)1) << MSb_POSITION_IN_MSB_DIGIT_OF_MODULUS;
 //print_pol(s, "s",NUM_DIGITS_GF2X_ELEMENT+1);
 //print_pol(r, "r",NUM_DIGITS_GF2X_ELEMENT+1);

 /* the paper states that these never exceed NUM_DIGITS_GF2X_ELEMENT+1,
  * FTTB I'll use 2*NUM_DIGITS_GF2X_ELEMENT, then trim */
 DIGIT v[NUM_DIGITS_GF2X_ELEMENT+1] = {0},
       u[NUM_DIGITS_GF2X_ELEMENT+1] = {0};

 u[NUM_DIGITS_GF2X_ELEMENT +1 -1] = (DIGIT) 2; /* x */

 int deg_r = NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_b -1;
 int deg_s = NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_b -1;

int l=0;
int l1=0;

 DIGIT c,d;
 DIGIT h00,h01,h10,h11;

 DIGIT hibitmask = ( (DIGIT) 1) << (DIGIT_SIZE_b-1);

 while(deg_r > 0){
     c=r[1];
     d=s[1];
     if(c == 0){
        left_DIGIT_shift_n(NUM_DIGITS_GF2X_ELEMENT+1,r,1);
        left_DIGIT_shift_n(NUM_DIGITS_GF2X_ELEMENT+1,u,1);
        // fprintf(stderr," BUCOOOOO deg_r: %d ",deg_r);
         deg_r = deg_r - DIGIT_SIZE_b;
     } else {
        /* H = I */
        h00 = 1; h01 = 0;
        h10 = 0; h11 = 1;
        for(int j = 1 ; (j < DIGIT_SIZE_b) && (deg_r > 0) ;j++) {
//           fprintf(stderr," deg_r, deg_s: %d,%d ",deg_r,deg_s);
           if ( (c & hibitmask) == 0){ /* */
               c = c << 1;
//          printf("\nH(x): %016lX ", h00);
//          printf(" %016lX\n", h01);
//          printf("      %016lX ", h10);
//          printf(" %016lX\n", h11);
               h00 = h00 << 1;
               h01 = h01 << 1;
               deg_r--;
//               fprintf(stderr," H1 ");
           } else { /* hibit r[0] set */
               if (deg_r == deg_s){
                 deg_r--;
                 if ( (d & hibitmask) == hibitmask){ /* hibit r[0],s[0] set, deg_r == deg_s */
                    DIGIT temp = c;
                    c = (c^d) << 1; /* (c-d)*x */
                    d = temp;
                    /*mult H*/
//                    fprintf(stderr," H2 ");
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
//                    fprintf(stderr," H3 ");
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
                  if ( (d & hibitmask) == hibitmask){ /* hibit r[0],s[0] set, deg_r != deg_s */
                     d = (c^d) << 1; /* (c-d) * x*/
                     /* mult H */
//                     fprintf(stderr," H4 ");
                     h10 = (h00 << 1) ^ (h10 << 1);
                     h11 = (h01 << 1) ^ (h11 << 1);
                  } else { /* hibit r[0] set, s[0] unset, deg_r != deg_s */
                     d = d << 1;
                     /*mul H*/
//          printf("\nH(x): %016lX ", h00);
//          printf(" %016lX\n", h01);
//          printf("      %016lX ", h10);
//          printf(" %016lX\n", h11);
//                    fprintf(stderr," H5 ");
                     h10 = h10 << 1;
                     h11 = h11 << 1;
                  }
               } /*(deg_r == deg_s)*/
           } /* if ( (c & ((DIGIT 1) << (DIGIT_SIZE_b-1))) == 0) */
        } /* while */
        /*update r , s */
//        fprintf(stderr, "\n** END OF DIGIT PROCESSING , Committing **\n");
//        print_pol(u, "u",2*NUM_DIGITS_GF2X_ELEMENT);
//        print_pol(v, "v",2*NUM_DIGITS_GF2X_ELEMENT);
//        print_pol(s, "s",NUM_DIGITS_GF2X_ELEMENT+1);
//        print_pol(r, "r",NUM_DIGITS_GF2X_ELEMENT+1);
//         printf("\nH(x): %016lX ", h00);
//         printf(" %016lX\n", h01);
//         printf("      %016lX ", h10);
//         printf(" %016lX\n\n", h11);

        DIGIT r_h00[NUM_DIGITS_GF2X_ELEMENT+2] = {0};
        DIGIT s_h01[NUM_DIGITS_GF2X_ELEMENT+2] = {0};
        DIGIT r_h10[NUM_DIGITS_GF2X_ELEMENT+2] = {0};
        DIGIT s_h11[NUM_DIGITS_GF2X_ELEMENT+2] = {0};

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

//         print_pol(r_h00, "r_h00",NUM_DIGITS_GF2X_ELEMENT+2);
//         print_pol(s_h01, "s_h01",NUM_DIGITS_GF2X_ELEMENT+2);
//         print_pol(r, "r_upd",NUM_DIGITS_GF2X_ELEMENT+1);


        gf2x_add(NUM_DIGITS_GF2X_ELEMENT+1, s,
                 NUM_DIGITS_GF2X_ELEMENT+1, r_h10+1,
                 NUM_DIGITS_GF2X_ELEMENT+1, s_h11+1);
//         print_pol(r_h10, "r_h10",NUM_DIGITS_GF2X_ELEMENT+2);
//         print_pol(s_h11, "s_h11",NUM_DIGITS_GF2X_ELEMENT+2);
//         print_pol(s, "s_upd",NUM_DIGITS_GF2X_ELEMENT+1);

        /* *********************** update u, v *************************/
        DIGIT  u_h00[NUM_DIGITS_GF2X_ELEMENT+2] = {0};
        DIGIT  v_h01[NUM_DIGITS_GF2X_ELEMENT+2] = {0};
        DIGIT  u_h10[NUM_DIGITS_GF2X_ELEMENT+2] = {0};
        DIGIT  v_h11[NUM_DIGITS_GF2X_ELEMENT+2] = {0};

        GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, u_h00,
                                  NUM_DIGITS_GF2X_ELEMENT+1, u,
                                  h00);
        GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, v_h01,
                                  NUM_DIGITS_GF2X_ELEMENT+1, v,
                                  h01);
        GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, u_h10,
                                  NUM_DIGITS_GF2X_ELEMENT+1, u,
                                  h10);
        GF2X_DIGIT_TIMES_POLY_MUL(NUM_DIGITS_GF2X_ELEMENT+2, v_h11,
                                  NUM_DIGITS_GF2X_ELEMENT+1, v,
                                  h11);

        /*turn this into CTIME*/
        if((v_h01[NUM_DIGITS_GF2X_ELEMENT+1] ^ u_h00[NUM_DIGITS_GF2X_ELEMENT+1])==0
            &&
            (v_h11[NUM_DIGITS_GF2X_ELEMENT+1] ^ u_h10[NUM_DIGITS_GF2X_ELEMENT+1])==0
            &&
            l1<NUM_DIGITS_GF2X_ELEMENT-1
        ){
            //right digit shift
            gf2x_add(NUM_DIGITS_GF2X_ELEMENT+1, u,
                    NUM_DIGITS_GF2X_ELEMENT+1, u_h00,
                    NUM_DIGITS_GF2X_ELEMENT+1, v_h01);

            gf2x_add(NUM_DIGITS_GF2X_ELEMENT+1, v,
                    NUM_DIGITS_GF2X_ELEMENT+1, u_h10,
                    NUM_DIGITS_GF2X_ELEMENT+1, v_h11);

                    l1++;
        }else{
            gf2x_add(NUM_DIGITS_GF2X_ELEMENT+1, u,
                    NUM_DIGITS_GF2X_ELEMENT+1, u_h00+1,
                    NUM_DIGITS_GF2X_ELEMENT+1, v_h01+1);

            gf2x_add(NUM_DIGITS_GF2X_ELEMENT+1, v,
                    NUM_DIGITS_GF2X_ELEMENT+1, u_h10+1,
                    NUM_DIGITS_GF2X_ELEMENT+1, v_h11+1);
        }
        l++;
     }
 }

 if (deg_r == 0) {
// fprintf(stderr,"out is U\n");
     /*output u / Mdigits */
  memcpy(out,u,NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
 }
 else {
 //fprintf(stderr,"out is V\n");
     /*output v / Mdigits */
  memcpy(out,v,NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
 }
#else
#error IMPLEMENT MEMCPY INTO A LARGER OPERAND
#endif

 return 0;
}

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/
/************************** DJB INVERSE AND RELATED FUNCTIONS *****************/
/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

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
        int l = na+nb+1;

        DIGIT   tmp[l];
        //memset(tmp,0x00,(na+nb)*DIGIT_SIZE_B);

        DIGIT  bufb[na];
        memset(bufb,0x00,(na-nb)*DIGIT_SIZE_B);
        memcpy(bufb+(na-nb),b0,nb*DIGIT_SIZE_B);
        GF2X_MUL(l,tmp, na,a0, na,bufb);

        DIGIT  tmp2[l];
        //memset(tmp2,0x00,(l)*DIGIT_SIZE_B);

        //memset(bufb,0x00,(na-nb)*DIGIT_SIZE_B);
        memcpy(bufb+(na-nb),b1,nb*DIGIT_SIZE_B);

        GF2X_MUL(l,tmp2, na,a1, na,bufb);

        gf2x_add(nr, Res, nr, tmp+l-nr, nr, tmp2+l-nr);

        //memcpy(Res,tmp2+(l-nr),nr*DIGIT_SIZE_B);

    } else /*nb > na*/ {

        DIGIT   tmp[2*nb];
        DIGIT tmp2[2*nb];
        DIGIT  bufa[nb];
        memset(bufa,0x00,(nb-na)*DIGIT_SIZE_B);
        memcpy(bufa+(nb-na),a0,na*DIGIT_SIZE_B);

        GF2X_MUL(nb*2,tmp, nb, bufa, nb,b0);

        //memset(bufa,0x00,(nb-na)*DIGIT_SIZE_B);
        memcpy(bufa+(nb-na),a1,na*DIGIT_SIZE_B);

        GF2X_MUL(nb*2,tmp2, nb,bufa, nb,b1);
        gf2x_add(nr, Res, nr, tmp+(nb*2)-nr, nr, tmp2+(nb*2)-nr);

    }
}

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

#define RS_MASK_256 _mm256_set_epi64x((DIGIT) 0x500000000, (DIGIT) 0x300000000, (DIGIT) 0x100000000, (DIGIT) 0x0)
static inline
__m256i right_shift_256(__m256i in){

    __m256i a,b;
    a = _mm256_srli_epi64(in,1);
    b = _mm256_slli_epi64(in,DIGIT_SIZE_b-1);

/*  V1 */
    b = _mm256_permute4x64_epi64(b,0x39);// == shift b by 64 bit and put the highest 64 to 0
    b = _mm256_insert_epi64(b, (DIGIT) 0, 0); //set the highest 64 bit to 0

/*  V2
    b = _mm256_permutevar8x32_epi32(b,RS_MASK_256);
*/
    a = _mm256_or_si256(a,b);

    return a;
}

/*************************************************************************/

#define CTIME_IF(mask,then,else)  ((mask&(then)) | (~mask&(else) ))
#define CTIME_IF_128(mask,then,else)  _mm_or_si128(_mm_and_si128(mask, then) ,_mm_andnot_si128(mask, else))
#define CTIME_IF_256(mask,then,else)  _mm256_blendv_epi8(else, then, mask)

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

    //  printf(" g64 : %lx\n", g64 );
    //  printf(" f64 : %lx\n", f64 );
    //  printf(" u : %lx\n", u );
    //  printf(" v : %lx\n", v );
    //  printf(" q : %lx\n", q );
     // printf(" r : %lx\n", r );

    // printf("********************\n");



   } //end while
    *p00 = u;
    *p01 = v;
    *p10 = q;
    *p11 = r;

    return delta;
}

int divstepsx_128(int n, int t,
              int delta,
              DIGIT f[], DIGIT g[],
              DIGIT * p00, DIGIT * p01,
              DIGIT * p10, DIGIT * p11)
{

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
//      print_pol((DIGIT *)&g128,"g128",2);
//      print_pol((DIGIT *)&f128,"f128",2);

      g0 = _mm_cmpeq_epi64(_mm_and_si128(g128, one_128), one_128);
      g0 = (__m128i)_mm_shuffle_pd((__m128d) g0, (__m128d) g0, 3);

      f0 = _mm_cmpeq_epi64(_mm_and_si128(f128, one_128), one_128);
      f0 = (__m128i)_mm_shuffle_pd((__m128d) f0, (__m128d) f0, 3);

//print_pol128(q,"q");
//print_pol128(r,"r");
      q =   _mm_xor_si128(_mm_and_si128(f0,q), _mm_and_si128(g0,u)); //(f0 & q) ^ (g0 & u);
      r =   _mm_xor_si128(_mm_and_si128(f0,r), _mm_and_si128(g0,v)); //(f0 & r) ^ (g0 & v);
      g128 = _mm_xor_si128(_mm_and_si128(f0,g128), _mm_and_si128(g0,f128)); //(f0 & g64) ^ (g0 & f64);


//print_pol128(q,"q");
//print_pol128(r,"r");


      g128 = right_shift_128(g128);
      q = right_shift_128(q);
      r = right_shift_128(r);
      n--;
      t--;

/*
      print_pol128(g128,"g128");
      print_pol128(f128,"f128");
      print_pol128(u,"u");
      print_pol128(v,"v");
      print_pol128(q,"q");
      print_pol128(r,"r");
*/

//printf("*********************\n" );

   } //end while
/*
   print_pol128(g128,"g128");
   print_pol128(f128,"f128");
   print_pol128(q,"q");
   print_pol128(r,"r");
   print_pol128(u,"u");
   print_pol128(v,"v");
 */

    _mm_storeu_si128((__m128i *) p00, u);
    _mm_storeu_si128((__m128i *) p01, v);
    _mm_storeu_si128((__m128i *) p10, q);
    _mm_storeu_si128((__m128i *) p11, r);

    return _mm_cvtsi128_si64x(delta_128);//_mm_extract_epi64(delta_128,1);
}


int divstepsx_256(int n, int t,
              int delta,
              DIGIT f[], DIGIT g[],
              DIGIT * p00, DIGIT * p01,
              DIGIT * p10, DIGIT * p11)
{
    if(n<127){
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

     //need to add 1 when changing sign
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

      g0 = _mm256_cmpeq_epi64(_mm256_and_si256(g256, one_256), one_256);
      g0 = _mm256_permute4x64_epi64(g256_mask, 0xFF);

      f0 = _mm256_cmpeq_epi64(_mm256_and_si256(f256, one_256), one_256);
      f0 = _mm256_permute4x64_epi64(g256_mask, 0xFF);

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

/*
      print_pol128(g128,"g128");
      print_pol128(f128,"f128");
      print_pol128(u,"u");
      print_pol128(v,"v");
      print_pol128(q,"q");
      print_pol128(r,"r");
*/

//printf("*********************\n" );

   } //end while
/*
   print_pol128(g128,"g128");
   print_pol128(f128,"f128");
   print_pol128(q,"q");
   print_pol128(r,"r");
   print_pol128(u,"u");
   print_pol128(v,"v");
 */

    _mm256_storeu_si256((__m256i *) p00, u);
    _mm256_storeu_si256((__m256i *) p01, v);
    _mm256_storeu_si256((__m256i *) p10, q);
    _mm256_storeu_si256((__m256i *) p11, r);

    return _mm256_extract_epi64(delta_256, 0);
}






/*  truncates polynomial inout to degree, zeroing other coefficients,
 *  returns pointer to truncated polynomial region */
DIGIT* gf2x_trunc(int inDigitLen, DIGIT inout[], int degree, DIGIT out2[]){

    if(degree > (inDigitLen*DIGIT_SIZE_b)){
        //printf("found inDigitLen = %i     degree = %i\n",inDigitLen*DIGIT_SIZE_b, degree );
        memset(out2,0x00, ((degree/DIGIT_SIZE_b)+1) * DIGIT_SIZE_B);
        memcpy(out2+((degree/DIGIT_SIZE_b)+1-inDigitLen),inout,inDigitLen*DIGIT_SIZE_B);
        return out2;
    }
    int straightIdx = (inDigitLen*DIGIT_SIZE_b -1) - degree;
    int digitIdx = straightIdx / DIGIT_SIZE_b;
    unsigned int inDigitIdx = straightIdx % DIGIT_SIZE_b;
    /*poly does not fill the MS digit, clear slack*/
    if(inDigitIdx != 0){
        DIGIT mask = (( (DIGIT) 1) << (DIGIT_SIZE_b-1-inDigitIdx+1))- ((DIGIT)1);
        inout[digitIdx] &= mask;
    }
    return inout+digitIdx;
}

int jumpdivstep(int n, int t, int delta,
                int nf, DIGIT   f[], DIGIT g[],
                DIGIT t00[], DIGIT t01[],
                DIGIT t10[], DIGIT t11[], float x)
{

#if (defined HIGH_COMPATIBILITY_X86_64 || defined HIGH_PERFORMANCE_X86_64)
    if (n <= 127) {
        return delta = divstepsx_128(n, t, delta,
                            f,
                            g,
                            t00, t01,
                            t10, t11);
    }
    int wordsize = 128;
#else

    if (n <= 63) {
        return delta = divstepsx(n, t, delta,
                            f[0],
                            g[0],
                            t00, t01,
                            t10, t11);
    }
    int wordsize = DIGIT_SIZE_b;

#endif

   /* round the cutting point to a digit limit */
  // printf("n=%i, x=%f, wordsize = %i\n",n,x,wordsize );

   int j = n*x;
   int j1 = n*x;

   j = (j+wordsize-2)/(wordsize-1);
   j1 = (j1+DIGIT_SIZE_b-2)/(DIGIT_SIZE_b-1);

   //printf("j2 = %i\n",j );

   j = j * (wordsize-1);
   j1 = j1 * (DIGIT_SIZE_b-1);

   //printf("j3 = %i\n",j );
   //printf("j/ws = %i\n",j/wordsize);

   int num_digits_j       = ((j/DIGIT_SIZE_b))+1; /* (j+DIGIT_SIZE_b-1)/DIGIT_SIZE_b */
   int num_digits_j1       = ((j1/DIGIT_SIZE_b))+1; /* (j+DIGIT_SIZE_b-1)/DIGIT_SIZE_b */
   if(num_digits_j != num_digits_j1){
       printf("num_digits_j = %i,  num_digits_j1 = %i\n",num_digits_j,num_digits_j1 );
       printf("n = %i, x=%f,    j = %i,  j1=%i\n",n,x,j,j1 );
   }

   DIGIT p_00[num_digits_j],p_01[num_digits_j],
         p_10[num_digits_j],p_11[num_digits_j];

 /*  memset(p_00,0x00,num_digits_j*DIGIT_SIZE_B);
   memset(p_01,0x00,num_digits_j*DIGIT_SIZE_B);
   memset(p_10,0x00,num_digits_j*DIGIT_SIZE_B);
   memset(p_11,0x00,num_digits_j*DIGIT_SIZE_B);
*/
   /* note: these local_f and local_g will be used by the downward call
    * they must be dup'ed and trimmed to the proper digit */
//printf("nf = %i, num_digits_j = %i\n",nf,num_digits_j );

   DIGIT local_f[num_digits_j];
   DIGIT local_g[num_digits_j];

   memcpy(local_f, f+(nf-num_digits_j), num_digits_j * DIGIT_SIZE_B);
   memcpy(local_g, g+(nf-num_digits_j), num_digits_j * DIGIT_SIZE_B);

   DIGIT trunc_f[j/DIGIT_SIZE_b+1];
   DIGIT trunc_g[j/DIGIT_SIZE_b+1];
//print_pol(local_g,"local_g",num_digits_j);

   delta = jumpdivstep(j, j, delta, num_digits_j,
                       gf2x_trunc(num_digits_j, local_f, j, trunc_f),
                       gf2x_trunc(num_digits_j, local_g, j, trunc_g),
                       p_00, p_01, p_10, p_11, x);
//printf("ok 1a jmp n=%i\n", n);

    //print_pol(p_00,"p_00",num_digits_j);
//    print_pol(p_01,"p_01";num_digits_j);


   /* note: entire f and g must be matrixmultiplied! use the ones from above */
  // if(nf> (num_digits_j*2+1)) printf("fail.");

   DIGIT f_sum[num_digits_j+nf];
   DIGIT g_sum[num_digits_j+nf];
   //printf("starting sp n=%i  nf = %i,   j=%i,  num_digits_j=%i\n", n,nf,j,num_digits_j);

   gf2x_scalarprod(num_digits_j+nf, f_sum,
                   num_digits_j,    p_00, p_01,
                   nf,                    f, g);
    //               printf("ok scalar1 n=%i\n", n);

   gf2x_scalarprod(num_digits_j+nf, g_sum,
                   num_digits_j,    p_10, p_11,
                   nf,                    f, g);
    //               printf("ok scalar2 n=%i\n", n);
//print_pol(p_10,"p10",num_digits_j);
//print_pol(p_11,"p11",num_digits_j);
//print_pol(g_sum,"gsum",num_digits_j+nf);


   right_bit_shift_wide_n(num_digits_j+nf, f_sum, j);
  // printf("ok shift f n=%i\n", n);
   right_bit_shift_wide_n(num_digits_j+nf, g_sum, j);
//printf("ok shift g n=%i\n", n);
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
//    print_pol(f_sum,"fsum",num_digits_j+nf);



    DIGIT  trunc_g2[(n-j)/DIGIT_SIZE_b+1];
    DIGIT  trunc_f2[(n-j)/DIGIT_SIZE_b+1];

   delta = jumpdivstep(n - j, n - j, delta,
                       num_digits_nminusj,
                       gf2x_trunc(num_digits_j+nf, f_sum, n-j, trunc_f2),
                       gf2x_trunc(num_digits_j+nf, g_sum, n-j, trunc_g2),
                       q_00, q_01, q_10, q_11, x);
//                       printf("ok 2a jmp n=%i\n", n);
//    print_pol(q_00,"q_00",num_digits_nminusj);
   DIGIT large_tmp[num_digits_j+num_digits_nminusj];
//   memset(large_tmp,0x00,(num_digits_j+num_digits_nminusj)*DIGIT_SIZE_B);


   gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                   num_digits_j,                    p_00, p_10,
                   num_digits_nminusj,                    q_00, q_01);
//    printf("ok t00\n");
   memcpy(t00,
          large_tmp+(num_digits_j+num_digits_nminusj-nf),
          (nf)*DIGIT_SIZE_B);

          //print_pol(t00,"t00",nf);


   gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                   num_digits_j,                    p_01, p_11,
                   num_digits_nminusj,                    q_00, q_01);
//                   printf("ok t01\n");

   memcpy(t01,
          large_tmp+(num_digits_j+num_digits_nminusj-nf),
          (nf)*DIGIT_SIZE_B);

   gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                   num_digits_j,                    p_00, p_10,
                   num_digits_nminusj,                    q_10, q_11);
//                   printf("ok t10\n");

   memcpy(t10,
          large_tmp+(num_digits_j+num_digits_nminusj-nf),
          (nf)*DIGIT_SIZE_B);

   gf2x_scalarprod(num_digits_j+num_digits_nminusj, large_tmp,
                   num_digits_j,                    p_01, p_11,
                   num_digits_nminusj,                    q_10, q_11);
//                   printf("ok t11\n");

   memcpy(t11,
          large_tmp+(num_digits_j+num_digits_nminusj-nf),
          (nf)*DIGIT_SIZE_B);

//   print_pol(t01,"t01",nf);
//   print_pol(t10,"t10",nf);
//   print_pol(t11,"t11",nf);
  // printf("fine  n=%i\n", n);
   return delta;
}

#define MATRIX_ELEM_DIGITS (NUM_DIGITS_GF2X_ELEMENT+2)
// #define MATRIX_ELEM_DIGITS ((2 * P - 1)/DIGIT_SIZE_b+1)
int inverse_DJB(DIGIT out[], const DIGIT in[], float x)
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

//           printf("matrix elem: %i   |  NUM_DIGITS_GF2X_ELEMENT:%i\n",MATRIX_ELEM_DIGITS,NUM_DIGITS_GF2X_ELEMENT );
//               printf("ok PRIMA JMPDV\n");
    delta = jumpdivstep(2 * P - 1, 2 * P - 1,
                        delta, MATRIX_ELEM_DIGITS,
                        largef, largeg, u, v, q, r, x);


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
    //printf("....................................................\n");

#else
#error IMPLEMENT MEMCPY INTO A LARGER OPERAND
#endif
    return 0;
}

/*************************************************************************/
/******  Funzioni di supporto al benchmarking  ****/
/*************************************************************************/
#define NUM_TESTS 100
// #define RANDOM_FILL

#define RANDOM_FILL
#if defined(RANDOM_FILL)
void generate_invertible_element(DIGIT input[NUM_DIGITS_GF2X_ELEMENT]){

    for (unsigned i = 0 ; i < 8*NUM_DIGITS_GF2X_ELEMENT ; i++){
         ((char*) input)[i] = rand();
    }

    int straightIdx = (NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_b -1) - P;
    unsigned int inDigitIdx = straightIdx % DIGIT_SIZE_b;
    /*poly does not fill the MS digit, clear slack*/
    if(inDigitIdx != 0){
        DIGIT mask = (( (DIGIT) 1) << (DIGIT_SIZE_b-1-inDigitIdx))- ((DIGIT)1);
        input[0] &= mask;
    }

    while( population_count(input) %2 != 1 ){
        for (unsigned i = 8*(NUM_DIGITS_GF2X_ELEMENT-1);
             i < 8*NUM_DIGITS_GF2X_ELEMENT;
             i++){
              ((char*) input)[i] = rand();
            }
    }
//     fprintf(stderr,"popcount is %d, %016lX\n",  population_count(input), input[0]);
}
#else

#endif





int main(int argc, char const *argv[])
{
    /************* inverse testing -- ok ************/

    DIGIT input[NUM_DIGITS_GF2X_ELEMENT] = { 0 };
    DIGIT out[NUM_DIGITS_GF2X_ELEMENT] = { 0 };
    DIGIT outcheck[NUM_DIGITS_GF2X_ELEMENT] = { 0 };

    generate_invertible_element(input);

    if(argc != 2){
        printf("inverse benchmarking routine (KTT vs DJB)\n Usage: %s <float>\n <float>  is the step for DJB cutting point exploration, should be <=0.5\n",argv[0]);
        return 1;
    }

    uint64_t start, end;

    welford_t KTT_timing, DJB_timing;
    welford_init(&KTT_timing);

    /* heat caches to minimize variance */
    gf2x_mod_inverse_KTT(outcheck,input);

    for(int i = 0; i < NUM_TESTS; i++) {
       start = x86_64_rtdsc();
       gf2x_mod_inverse_KTT(outcheck,input);
       end = x86_64_rtdsc();
       welford_update(&KTT_timing, ((long double) (end-start)));
    }
    welford_print(KTT_timing);
    gf2x_mod_mul(out, outcheck, input);
    int is_result_one = 1;
    for(int i = 0; i<NUM_DIGITS_GF2X_ELEMENT-1; i++){
        if(out[i] != (DIGIT) 0)
            is_result_one = 0;
    }
    if(out[NUM_DIGITS_GF2X_ELEMENT-1] != (DIGIT) 1){
        is_result_one = 0;
    }
    if (!is_result_one) printf("    check failed\n");
    memset(out,0x00,NUM_DIGITS_GF2X_ELEMENT*DIGIT_SIZE_B);
    printf("\n");

    float splitting_portion, splitting_step;
    splitting_step = atof(argv[1]);
    splitting_portion = splitting_step;

    while(! (splitting_portion > 0.51)) { //while(! (splitting_portion > 0.5+splitting_step))
       generate_invertible_element(input);
       welford_init(&DJB_timing);

       for(int i = 0; i < NUM_TESTS; i++) {
          start = x86_64_rtdsc();
          inverse_DJB(outcheck,input, splitting_portion);
          end = x86_64_rtdsc();
          welford_update(&DJB_timing, ((long double) (end-start)));
       }
//              printf ("ok -1\n");
       welford_print(DJB_timing);
       printf(",%.2f\n ",splitting_portion);
//              printf ("ok0\n");
       gf2x_mod_mul(out, outcheck, input);
       int is_result_one = 1;
//       printf ("ok1\n");
       for(int i = 0; i<NUM_DIGITS_GF2X_ELEMENT-1; i++){
           if(out[i] != (DIGIT) 0)
               is_result_one = 0;
       }
//       printf("ok2");
       if(out[NUM_DIGITS_GF2X_ELEMENT-1] != (DIGIT) 1){
           is_result_one = 0;
       }
       if (!is_result_one) printf("check failed\n");
       splitting_portion += splitting_step;
    }
/*
    __m256i prova = _mm256_set_epi64x((DIGIT) 1, (DIGIT) 1,(DIGIT) 1, (DIGIT) 1);
    print_pol256(prova,"start");
    prova = right_shift_256(prova);
    print_pol256(prova,"prova 1");
*/


    return 0;
}
