#include "api.h"
#include <string.h>
#include <stdio.h>

void fprintBstr(FILE *fp, char *S, unsigned char *A, unsigned long long L);

int main(void ) {

 unsigned char pk[CRYPTO_PUBLICKEYBYTES];
 unsigned char sk[CRYPTO_SECRETKEYBYTES];

unsigned char ct[CRYPTO_CIPHERTEXTBYTES];

unsigned char ss[CRYPTO_BYTES];

FILE *fl;
fl = fopen("file", "w");

 printf("generating....");

 int bob = crypto_kem_keypair( pk, sk);


 if(bob != 0 ){
     return 1;
    }
 printf("done\n");

 fprintBstr(fl, "pk = ", pk, CRYPTO_PUBLICKEYBYTES);
 fprintBstr(fl, "sk = ", sk, CRYPTO_SECRETKEYBYTES);
 fprintBstr(fl, "ct = ", ct, CRYPTO_CIPHERTEXTBYTES);


bob= crypto_kem_enc( ct, ss, pk);


 if(bob != 0 ){
     return 2;
    }

    fprintBstr(fl, "ss = ", ss, CRYPTO_BYTES);
    fprintBstr(fl, "ct2 = ", ct, CRYPTO_CIPHERTEXTBYTES);


bob = crypto_kem_dec(ss, ct, sk);


 if(bob != 0 ){
     return 3;
    }

    fprintBstr(fl, "ct3 = ", ct, CRYPTO_CIPHERTEXTBYTES);


    return 0;
}   //end main

void fprintBstr(FILE *fp, char *S, unsigned char *A, unsigned long long L)
{
	unsigned long long  i;

	fprintf(fp, "%s", S);

	for ( i=0; i<L; i++ )
		fprintf(fp, "%02X", A[i]);

	if ( L == 0 )
		fprintf(fp, "00");

	fprintf(fp, "\n");
}
