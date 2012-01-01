/*-
 * Copyright 2009 Colin Percival, 2011 ArtForz, 2011 pooler
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file was originally written by Colin Percival as part of the Tarsnap
 * online backup system.
 */

#include "cpuminer-config.h"
#include "miner.h"

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "sha256-helpers.h"
#include "scrypt-simd-helpers.h"

/**
 * salsa20_8(B):
 * Apply the salsa20/8 core to the provided block.
 */
static inline void
salsa20_8(uint32_t B[16], const uint32_t Bx[16])
{
	uint32_t x00,x01,x02,x03,x04,x05,x06,x07,x08,x09,x10,x11,x12,x13,x14,x15;
	size_t i;

	x00 = (B[ 0] ^= Bx[ 0]);
	x01 = (B[ 1] ^= Bx[ 1]);
	x02 = (B[ 2] ^= Bx[ 2]);
	x03 = (B[ 3] ^= Bx[ 3]);
	x04 = (B[ 4] ^= Bx[ 4]);
	x05 = (B[ 5] ^= Bx[ 5]);
	x06 = (B[ 6] ^= Bx[ 6]);
	x07 = (B[ 7] ^= Bx[ 7]);
	x08 = (B[ 8] ^= Bx[ 8]);
	x09 = (B[ 9] ^= Bx[ 9]);
	x10 = (B[10] ^= Bx[10]);
	x11 = (B[11] ^= Bx[11]);
	x12 = (B[12] ^= Bx[12]);
	x13 = (B[13] ^= Bx[13]);
	x14 = (B[14] ^= Bx[14]);
	x15 = (B[15] ^= Bx[15]);
	for (i = 0; i < 8; i += 2) {
#define R(a,b) (((a) << (b)) | ((a) >> (32 - (b))))
		/* Operate on columns. */
		x04 ^= R(x00+x12, 7);	x09 ^= R(x05+x01, 7);	x14 ^= R(x10+x06, 7);	x03 ^= R(x15+x11, 7);
		x08 ^= R(x04+x00, 9);	x13 ^= R(x09+x05, 9);	x02 ^= R(x14+x10, 9);	x07 ^= R(x03+x15, 9);
		x12 ^= R(x08+x04,13);	x01 ^= R(x13+x09,13);	x06 ^= R(x02+x14,13);	x11 ^= R(x07+x03,13);
		x00 ^= R(x12+x08,18);	x05 ^= R(x01+x13,18);	x10 ^= R(x06+x02,18);	x15 ^= R(x11+x07,18);

		/* Operate on rows. */
		x01 ^= R(x00+x03, 7);	x06 ^= R(x05+x04, 7);	x11 ^= R(x10+x09, 7);	x12 ^= R(x15+x14, 7);
		x02 ^= R(x01+x00, 9);	x07 ^= R(x06+x05, 9);	x08 ^= R(x11+x10, 9);	x13 ^= R(x12+x15, 9);
		x03 ^= R(x02+x01,13);	x04 ^= R(x07+x06,13);	x09 ^= R(x08+x11,13);	x14 ^= R(x13+x12,13);
		x00 ^= R(x03+x02,18);	x05 ^= R(x04+x07,18);	x10 ^= R(x09+x08,18);	x15 ^= R(x14+x13,18);
#undef R
	}
	B[ 0] += x00;
	B[ 1] += x01;
	B[ 2] += x02;
	B[ 3] += x03;
	B[ 4] += x04;
	B[ 5] += x05;
	B[ 6] += x06;
	B[ 7] += x07;
	B[ 8] += x08;
	B[ 9] += x09;
	B[10] += x10;
	B[11] += x11;
	B[12] += x12;
	B[13] += x13;
	B[14] += x14;
	B[15] += x15;
}

static inline void scrypt_core1(uint32_t *X, uint32_t *V)
{
	uint32_t i;
	uint32_t j;
	uint32_t k;
	uint32_t *p1, *p2;
	p1 = X;
	for (i = 0; i < 1024; i += 2) {
		memcpy(&V[i * 32], X, 128);

		salsa20_8(&X[0], &X[16]);
		salsa20_8(&X[16], &X[0]);

		memcpy(&V[(i + 1) * 32], X, 128);

		salsa20_8(&X[0], &X[16]);
		salsa20_8(&X[16], &X[0]);
	}
	for (i = 0; i < 1024; i += 2) {
		j = X[16] & 1023;
		p2 = &V[j * 32];
		for(k = 0; k < 32; k++)
			p1[k] ^= p2[k];

		salsa20_8(&X[0], &X[16]);
		salsa20_8(&X[16], &X[0]);

		j = X[16] & 1023;
		p2 = &V[j * 32];
		for(k = 0; k < 32; k++)
			p1[k] ^= p2[k];

		salsa20_8(&X[0], &X[16]);
		salsa20_8(&X[16], &X[0]);
	}
}


/* cpu and memory intensive function to transform a 80 byte buffer into a 32 byte output
   scratchpad size needs to be at least 63 + (128 * r * p) + (256 * r + 64) + (128 * r * N) bytes
 */
static void scrypt_1024_1_1_256_sp1(const uint32_t* input, uint32_t* output, uint8_t* scratchpad)
{
	uint32_t tstate[8], ostate[8];
	uint32_t * B;
	uint32_t * V;

	B = (uint32_t *)(((uintptr_t)(scratchpad) + 63) & ~ (uintptr_t)(63));
	V = (uint32_t *)(B + 32);

	PBKDF2_SHA256_80_128_init(input, tstate, ostate);
	PBKDF2_SHA256_80_128(tstate, ostate, input, B);

#ifdef HAVE_SCRYPT_SIMD_HELPERS
	scrypt_simd_core1(B, V);
#else
	scrypt_core1(B, V);
#endif

	PBKDF2_SHA256_80_128_32(tstate, ostate, input, B, output);
}

int scanhash_scrypt1(int thr_id, unsigned char *pdata, uint8_t *scratchbuf,
	const unsigned char *ptarget,
	uint32_t max_nonce, unsigned long *hashes_done)
{
	uint32_t data[20];
	uint32_t tmp_hash[32];
	uint32_t *nonce = (uint32_t *)(data + 19);
	uint32_t n = 0;
	uint32_t Htarg = le32dec(ptarget + 28);
	int i;

	work_restart[thr_id].restart = 0;
	
	for (i = 0; i < 80/4; i++)
		data[i] = be32dec(pdata + i * 4);
	
	while(1) {
		n++;
		*nonce = n;
		scrypt_1024_1_1_256_sp1(data, tmp_hash, scratchbuf);

		if (tmp_hash[7] <= Htarg) {
			be32enc(pdata + 64 + 12, n);
			*hashes_done = n;
			return true;
		}

		if ((n >= max_nonce) || work_restart[thr_id].restart) {
			*hashes_done = n;
			break;
		}
	}
	return false;
}

#ifdef HAVE_SCRYPT_SIMD_HELPERS

static void
scrypt_1024_1_1_256_sp2(const uint32_t * input1,
                        uint32_t       * output1,
                        const uint32_t * input2,
                        uint32_t       * output2,
                        uint8_t        * scratchpad)
{
	uint32_t tstate1[8], tstate2[8], ostate1[8], ostate2[8];
	uint32_t * B1, * B2;
	uint32_t * V;

	B1 = (uint32_t *)(((uintptr_t)(scratchpad) + 63) & ~ (uintptr_t)(63));
	B2 = B1 + 32;
	V  = B2 + 32;

	PBKDF2_SHA256_80_128_init(input1, tstate1, ostate1);
	PBKDF2_SHA256_80_128_init(input2, tstate2, ostate2);
	PBKDF2_SHA256_80_128(tstate1, ostate1, input1, B1);
	PBKDF2_SHA256_80_128(tstate2, ostate2, input2, B2);

	scrypt_simd_core2(B1, V);

	PBKDF2_SHA256_80_128_32(tstate1, ostate1, input1, B1, output1);
	PBKDF2_SHA256_80_128_32(tstate2, ostate2, input2, B2, output2);
}

int scanhash_scrypt2(int thr_id, unsigned char *pdata, unsigned char *scratchbuf,
	const unsigned char *ptarget,
	uint32_t max_nonce, unsigned long *hashes_done)
{
	uint32_t data1[20];
	uint32_t tmp_hash1[8];
	uint32_t data2[20];
	uint32_t tmp_hash2[8];
	uint32_t *nonce1 = (uint32_t *)(data1 + 19);
	uint32_t *nonce2 = (uint32_t *)(data2 + 19);
	uint32_t n = 0;
	uint32_t Htarg = le32dec(ptarget + 28);
	int i;

	work_restart[thr_id].restart = 0;
	
	for (i = 0; i < 80/4; i++) {
		((uint32_t *)data1)[i] = be32dec(pdata + i * 4);
		((uint32_t *)data2)[i] = be32dec(pdata + i * 4);
	}
	
	while(1) {
		*nonce1 = n + 1;
		*nonce2 = n + 2;
		scrypt_1024_1_1_256_sp2(data1, tmp_hash1, data2, tmp_hash2, scratchbuf);

		if (tmp_hash1[7] <= Htarg) {
			be32enc(pdata + 64 + 12, n + 1);
			*hashes_done = n + 1;
			return true;
		}

		if (tmp_hash2[7] <= Htarg && n + 2 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 2);
			*hashes_done = n + 2;
			return true;
		}

		n += 2;

		if (n >= max_nonce) {
			*hashes_done = max_nonce;
			break;
		}

		if (work_restart[thr_id].restart) {
			*hashes_done = n;
			break;
		}
	}
	return false;
}

#endif

int scanhash_scrypt(int thr_id, unsigned char *pdata, unsigned char *scratchbuf,
	const unsigned char *ptarget,
	uint32_t max_nonce, unsigned long *hashes_done)
{
	/*
	 * TODO: maybe add a command line option or run benchmarks at start
	 * to select the fastest implementation?
	 */
#ifdef HAVE_SCRYPT_SIMD_HELPERS
	return scanhash_scrypt2(thr_id, pdata, scratchbuf, ptarget, max_nonce, hashes_done);
#else
	return scanhash_scrypt1(thr_id, pdata, scratchbuf, ptarget, max_nonce, hashes_done);
#endif
}
