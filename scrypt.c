/*-
 * Copyright 2009 Colin Percival, 2011 ArtForz
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

static void blkcpy(void *, void *, size_t);
static void blkxor(void *, void *, size_t);
static void salsa20_8(uint32_t[16]);
static void blockmix_salsa8(uint32_t *, uint32_t *, uint32_t *, size_t);
static uint64_t integerify(void *, size_t);
static void smix(uint8_t *, size_t, uint64_t, uint32_t *, uint32_t *);

static void
blkcpy(void * dest, void * src, size_t len)
{
	size_t * D = dest;
	size_t * S = src;
	size_t L = len / sizeof(size_t);
	size_t i;

	for (i = 0; i < L; i++)
		D[i] = S[i];
}

static void
blkxor(void * dest, void * src, size_t len)
{
	size_t * D = dest;
	size_t * S = src;
	size_t L = len / sizeof(size_t);
	size_t i;

	for (i = 0; i < L; i++)
		D[i] ^= S[i];
}

/**
 * salsa20_8(B):
 * Apply the salsa20/8 core to the provided block.
 */
static void
salsa20_8(uint32_t B[16])
{
	uint32_t x[16];
	size_t i;

	blkcpy(x, B, 64);
	for (i = 0; i < 8; i += 2) {
#define R(a,b) (((a) << (b)) | ((a) >> (32 - (b))))
		/* Operate on columns. */
		x[ 4] ^= R(x[ 0]+x[12], 7);  x[ 8] ^= R(x[ 4]+x[ 0], 9);
		x[12] ^= R(x[ 8]+x[ 4],13);  x[ 0] ^= R(x[12]+x[ 8],18);

		x[ 9] ^= R(x[ 5]+x[ 1], 7);  x[13] ^= R(x[ 9]+x[ 5], 9);
		x[ 1] ^= R(x[13]+x[ 9],13);  x[ 5] ^= R(x[ 1]+x[13],18);

		x[14] ^= R(x[10]+x[ 6], 7);  x[ 2] ^= R(x[14]+x[10], 9);
		x[ 6] ^= R(x[ 2]+x[14],13);  x[10] ^= R(x[ 6]+x[ 2],18);

		x[ 3] ^= R(x[15]+x[11], 7);  x[ 7] ^= R(x[ 3]+x[15], 9);
		x[11] ^= R(x[ 7]+x[ 3],13);  x[15] ^= R(x[11]+x[ 7],18);

		/* Operate on rows. */
		x[ 1] ^= R(x[ 0]+x[ 3], 7);  x[ 2] ^= R(x[ 1]+x[ 0], 9);
		x[ 3] ^= R(x[ 2]+x[ 1],13);  x[ 0] ^= R(x[ 3]+x[ 2],18);

		x[ 6] ^= R(x[ 5]+x[ 4], 7);  x[ 7] ^= R(x[ 6]+x[ 5], 9);
		x[ 4] ^= R(x[ 7]+x[ 6],13);  x[ 5] ^= R(x[ 4]+x[ 7],18);

		x[11] ^= R(x[10]+x[ 9], 7);  x[ 8] ^= R(x[11]+x[10], 9);
		x[ 9] ^= R(x[ 8]+x[11],13);  x[10] ^= R(x[ 9]+x[ 8],18);

		x[12] ^= R(x[15]+x[14], 7);  x[13] ^= R(x[12]+x[15], 9);
		x[14] ^= R(x[13]+x[12],13);  x[15] ^= R(x[14]+x[13],18);
#undef R
	}
	for (i = 0; i < 16; i++)
		B[i] += x[i];
}

/**
 * blockmix_salsa8(Bin, Bout, X, r):
 * Compute Bout = BlockMix_{salsa20/8, r}(Bin).  The input Bin must be 128r
 * bytes in length; the output Bout must also be the same size.  The
 * temporary space X must be 64 bytes.
 */
static void
blockmix_salsa8(uint32_t * Bin, uint32_t * Bout, uint32_t * X, size_t r)
{
	size_t i;

	/* 1: X <-- B_{2r - 1} */
	blkcpy(X, &Bin[(2 * r - 1) * 16], 64);

	/* 2: for i = 0 to 2r - 1 do */
	for (i = 0; i < 2 * r; i += 2) {
		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 16], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[i * 8], X, 64);

		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 16 + 16], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[i * 8 + r * 16], X, 64);
	}
}

/**
 * integerify(B, r):
 * Return the result of parsing B_{2r-1} as a little-endian integer.
 */
static uint64_t
integerify(void * B, size_t r)
{
	uint32_t * X = (void *)((uintptr_t)(B) + (2 * r - 1) * 64);

	return (((uint64_t)(X[1]) << 32) + X[0]);
}

/**
 * smix(B, r, N, V, XY):
 * Compute B = SMix_r(B, N).  The input B must be 128r bytes in length;
 * the temporary storage V must be 128rN bytes in length; the temporary
 * storage XY must be 256r + 64 bytes in length.  The value N must be a
 * power of 2 greater than 1.  The arrays B, V, and XY must be aligned to a
 * multiple of 64 bytes.
 */
static void
smix(uint8_t * B, size_t r, uint64_t N, uint32_t * V, uint32_t * XY)
{
	uint32_t * X = XY;
	uint32_t * Y = &XY[32 * r];
	uint32_t * Z = &XY[64 * r];
	uint64_t i;
	uint64_t j;
	size_t k;

	/* 1: X <-- B */
	for (k = 0; k < 32 * r; k++)
		X[k] = le32dec(&B[4 * k]);

	/* 2: for i = 0 to N - 1 do */
	for (i = 0; i < N; i += 2) {
		/* 3: V_i <-- X */
		blkcpy(&V[i * (32 * r)], X, 128 * r);

		/* 4: X <-- H(X) */
		blockmix_salsa8(X, Y, Z, r);

		/* 3: V_i <-- X */
		blkcpy(&V[(i + 1) * (32 * r)], Y, 128 * r);

		/* 4: X <-- H(X) */
		blockmix_salsa8(Y, X, Z, r);
	}

	/* 6: for i = 0 to N - 1 do */
	for (i = 0; i < N; i += 2) {
		/* 7: j <-- Integerify(X) mod N */
		j = integerify(X, r) & (N - 1);

		/* 8: X <-- H(X \xor V_j) */
		blkxor(X, &V[j * (32 * r)], 128 * r);
		blockmix_salsa8(X, Y, Z, r);

		/* 7: j <-- Integerify(X) mod N */
		j = integerify(Y, r) & (N - 1);

		/* 8: X <-- H(X \xor V_j) */
		blkxor(Y, &V[j * (32 * r)], 128 * r);
		blockmix_salsa8(Y, X, Z, r);
	}

	/* 10: B' <-- X */
	for (k = 0; k < 32 * r; k++)
		le32enc(&B[4 * k], X[k]);
}

/* cpu and memory intensive function to transform a 80 byte buffer into a 32 byte output
   scratchpad size needs to be at least 63 + (128 * r * p) + (256 * r + 64) + (128 * r * N) bytes
 */
static void scrypt_1024_1_1_256_sp1(const char* input, char* output, char* scratchpad)
{
	uint8_t * B;
	uint32_t * V;
	uint32_t * XY;
	uint32_t i;

	const uint32_t N = 1024;
	const uint32_t r = 1;
	const uint32_t p = 1;

	B = (uint8_t *)(((uintptr_t)(scratchpad) + 63) & ~ (uintptr_t)(63));
	XY = (uint32_t *)(B + (128 * r * p));
	V = (uint32_t *)(B + (128 * r * p) + (256 * r + 64));

	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input, 80, (const uint8_t*)input, 80, 1, B, p * 128 * r);

#ifdef HAVE_SCRYPT_SIMD_HELPERS
	scrypt_simd_core1(B, XY);
#else
	/* 2: for i = 0 to p - 1 do */
	for (i = 0; i < p; i++) {
		/* 3: B_i <-- MF(B_i, N) */
		smix(&B[i * 128 * r], r, N, V, XY);
	}
#endif

	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input, 80, B, p * 128 * r, 1, (uint8_t*)output, 32);
}

int scanhash_scrypt1(int thr_id, unsigned char *pdata, unsigned char *scratchbuf,
	const unsigned char *ptarget,
	uint32_t max_nonce, unsigned long *hashes_done)
{
	unsigned char data[80];
	unsigned char tmp_hash[32];
	uint32_t *nonce = (uint32_t *)(data + 64 + 12);
	uint32_t n = 0;
	uint32_t Htarg = le32dec(ptarget + 28);
	int i;

	work_restart[thr_id].restart = 0;
	
	for (i = 0; i < 80/4; i++)
		((uint32_t *)data)[i] = swab32(((uint32_t *)pdata)[i]);
	
	while(1) {
		n++;
		le32enc(nonce, n);
		scrypt_1024_1_1_256_sp1(data, tmp_hash, scratchbuf);

		if (le32dec(tmp_hash+28) <= Htarg) {
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
scrypt_1024_1_1_256_sp2(const unsigned char * input1,
                        unsigned char       * output1,
                        const unsigned char * input2,
                        unsigned char       * output2,
                        unsigned char       * scratchpad)
{
	uint8_t * B1, * B2;
	uint8_t * V;

	const uint32_t N = 1024;
	const uint32_t r = 1;
	const uint32_t p = 1;

	B1 = (uint8_t *)(((uintptr_t)(scratchpad) + 63) & ~ (uintptr_t)(63));
	B2 = B1 + 128;
	V  = B2 + 128;

	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input1, 80, (const uint8_t*)input1, 80, 1, B1, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input2, 80, (const uint8_t*)input2, 80, 1, B2, p * 128 * r);

	scrypt_simd_core2(B1, V);

	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input1, 80, B1, p * 128 * r, 1, (uint8_t*)output1, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input2, 80, B2, p * 128 * r, 1, (uint8_t*)output2, 32);
}

int scanhash_scrypt2(int thr_id, unsigned char *pdata, unsigned char *scratchbuf,
	const unsigned char *ptarget,
	uint32_t max_nonce, unsigned long *hashes_done)
{
	unsigned char data1[80];
	unsigned char tmp_hash1[32];
	unsigned char data2[80];
	unsigned char tmp_hash2[32];
	uint32_t *nonce1 = (uint32_t *)(data1 + 64 + 12);
	uint32_t *nonce2 = (uint32_t *)(data2 + 64 + 12);
	uint32_t n = 0;
	uint32_t Htarg = le32dec(ptarget + 28);
	int i;

	work_restart[thr_id].restart = 0;
	
	for (i = 0; i < 80/4; i++) {
		((uint32_t *)data1)[i] = swab32(((uint32_t *)pdata)[i]);
		((uint32_t *)data2)[i] = swab32(((uint32_t *)pdata)[i]);
	}
	
	while(1) {
		le32enc(nonce1, n + 1);
		le32enc(nonce2, n + 2);
		scrypt_1024_1_1_256_sp2(data1, tmp_hash1, data2, tmp_hash2, scratchbuf);

		if (le32dec(tmp_hash1+28) <= Htarg) {
			be32enc(pdata + 64 + 12, n + 1);
			*hashes_done = n + 1;
			return true;
		}

		if (le32dec(tmp_hash2+28) <= Htarg && n + 2 <= max_nonce) {
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
