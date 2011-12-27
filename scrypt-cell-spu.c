/*-
 * Copyright 2009 Colin Percival, 2011 ArtForz, 2011 Siarhei Siamashka
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

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include <spu_intrinsics.h>
#include <spu_mfcio.h>

#include "sha256-helpers.h"
#include "scrypt-simd-helpers.h"
#include "scrypt-cell-spu.h"

#define true 1
#define false 0

/*****************************************************************************/

static __attribute__((always_inline)) void
salsa20_8_xor4(uint32x4 * __restrict B, const uint32x4 * __restrict Bx,
               uint32x4 * __restrict C, const uint32x4 * __restrict Cx,
               uint32x4 * __restrict D, const uint32x4 * __restrict Dx,
               uint32x4 * __restrict E, const uint32x4 * __restrict Ex)
{
	uint32x4 X0, X1, X2, X3;
	uint32x4 Y0, Y1, Y2, Y3;
	uint32x4 Z0, Z1, Z2, Z3;
	uint32x4 W0, W1, W2, W3;
	int i;

	X0 = (B[0] ^= Bx[0]);
	X1 = (B[1] ^= Bx[1]);
	X2 = (B[2] ^= Bx[2]);
	X3 = (B[3] ^= Bx[3]);
	Y0 = (C[0] ^= Cx[0]);
	Y1 = (C[1] ^= Cx[1]);
	Y2 = (C[2] ^= Cx[2]);
	Y3 = (C[3] ^= Cx[3]);
	Z0 = (D[0] ^= Dx[0]);
	Z1 = (D[1] ^= Dx[1]);
	Z2 = (D[2] ^= Dx[2]);
	Z3 = (D[3] ^= Dx[3]);
	W0 = (E[0] ^= Ex[0]);
	W1 = (E[1] ^= Ex[1]);
	W2 = (E[2] ^= Ex[2]);
	W3 = (E[3] ^= Ex[3]);

	for (i = 0; i < 8; i += 2) {
		/* Operate on "columns". */
		X1 ^= rol_32x4(X0 + X3, 7);
		Y1 ^= rol_32x4(Y0 + Y3, 7);
		Z1 ^= rol_32x4(Z0 + Z3, 7);
		W1 ^= rol_32x4(W0 + W3, 7);
		X2 ^= rol_32x4(X1 + X0, 9);
		Y2 ^= rol_32x4(Y1 + Y0, 9);
		Z2 ^= rol_32x4(Z1 + Z0, 9);
		W2 ^= rol_32x4(W1 + W0, 9);
		X3 ^= rol_32x4(X2 + X1, 13);
		Y3 ^= rol_32x4(Y2 + Y1, 13);
		Z3 ^= rol_32x4(Z2 + Z1, 13);
		W3 ^= rol_32x4(W2 + W1, 13);
		X0 ^= rol_32x4(X3 + X2, 18);
		Y0 ^= rol_32x4(Y3 + Y2, 18);
		Z0 ^= rol_32x4(Z3 + Z2, 18);
		W0 ^= rol_32x4(W3 + W2, 18);

		/* Rearrange data. */
		X1 = shuffle_32x4(X1, 3, 0, 1, 2);
		Y1 = shuffle_32x4(Y1, 3, 0, 1, 2);
		Z1 = shuffle_32x4(Z1, 3, 0, 1, 2);
		W1 = shuffle_32x4(W1, 3, 0, 1, 2);
		X2 = shuffle_32x4(X2, 2, 3, 0, 1);
		Y2 = shuffle_32x4(Y2, 2, 3, 0, 1);
		Z2 = shuffle_32x4(Z2, 2, 3, 0, 1);
		W2 = shuffle_32x4(W2, 2, 3, 0, 1);
		X3 = shuffle_32x4(X3, 1, 2, 3, 0);
		Y3 = shuffle_32x4(Y3, 1, 2, 3, 0);
		Z3 = shuffle_32x4(Z3, 1, 2, 3, 0);
		W3 = shuffle_32x4(W3, 1, 2, 3, 0);

		/* Operate on "rows". */
		X3 ^= rol_32x4(X0 + X1, 7);
		Y3 ^= rol_32x4(Y0 + Y1, 7);
		Z3 ^= rol_32x4(Z0 + Z1, 7);
		W3 ^= rol_32x4(W0 + W1, 7);
		X2 ^= rol_32x4(X3 + X0, 9);
		Y2 ^= rol_32x4(Y3 + Y0, 9);
		Z2 ^= rol_32x4(Z3 + Z0, 9);
		W2 ^= rol_32x4(W3 + W0, 9);
		X1 ^= rol_32x4(X2 + X3, 13);
		Y1 ^= rol_32x4(Y2 + Y3, 13);
		Z1 ^= rol_32x4(Z2 + Z3, 13);
		W1 ^= rol_32x4(W2 + W3, 13);
		X0 ^= rol_32x4(X1 + X2, 18);
		Y0 ^= rol_32x4(Y1 + Y2, 18);
		Z0 ^= rol_32x4(Z1 + Z2, 18);
		W0 ^= rol_32x4(W1 + W2, 18);

		/* Rearrange data. */
		X1 = shuffle_32x4(X1, 1, 2, 3, 0);
		Y1 = shuffle_32x4(Y1, 1, 2, 3, 0);
		Z1 = shuffle_32x4(Z1, 1, 2, 3, 0);
		W1 = shuffle_32x4(W1, 1, 2, 3, 0);
		X2 = shuffle_32x4(X2, 2, 3, 0, 1);
		Y2 = shuffle_32x4(Y2, 2, 3, 0, 1);
		Z2 = shuffle_32x4(Z2, 2, 3, 0, 1);
		W2 = shuffle_32x4(W2, 2, 3, 0, 1);
		X3 = shuffle_32x4(X3, 3, 0, 1, 2);
		Y3 = shuffle_32x4(Y3, 3, 0, 1, 2);
		Z3 = shuffle_32x4(Z3, 3, 0, 1, 2);
		W3 = shuffle_32x4(W3, 3, 0, 1, 2);
	}

	B[0] += X0;
	B[1] += X1;
	B[2] += X2;
	B[3] += X3;
	C[0] += Y0;
	C[1] += Y1;
	C[2] += Y2;
	C[3] += Y3;
	D[0] += Z0;
	D[1] += Z1;
	D[2] += Z2;
	D[3] += Z3;
	E[0] += W0;
	E[1] += W1;
	E[2] += W2;
	E[3] += W3;
}

static void
scrypt_spu_core8(uint8_t *databuf, uint64_t scratch)
{
	static mfc_list_element_t dma_list[8] __attribute__((aligned(128)));
	static XY X[8] __attribute__((aligned(128)));
	static uint32x4 Y[8 * 8] __attribute__((aligned(128)));
	static uint32x4 Z[8 * 8] __attribute__((aligned(128)));
	XY       * XA = &X[0];
	XY       * XB = &X[1];
	XY       * XC = &X[2];
	XY       * XD = &X[3];
	XY       * XE = &X[4];
	XY       * XF = &X[5];
	XY       * XG = &X[6];
	XY       * XH = &X[7];

	uint64_t VA = (scratch + 128 * 1024 * 0);
	uint64_t VB = (scratch + 128 * 1024 * 1);
	uint64_t VC = (scratch + 128 * 1024 * 2);
	uint64_t VD = (scratch + 128 * 1024 * 3);
	uint64_t VE = (scratch + 128 * 1024 * 4);
	uint64_t VF = (scratch + 128 * 1024 * 5);
	uint64_t VG = (scratch + 128 * 1024 * 6);
	uint64_t VH = (scratch + 128 * 1024 * 7);
	int i;
	int tag1 = 1, tag_mask1 = 1 << tag1;
	int tag2 = 2, tag_mask2 = 1 << tag2;

	/* 1: X <-- B */
	for (i = 0; i < 16; i++) {
		XA->w[i]      = le32dec(&databuf[0 * 128 + (i * 5 % 16) * 4]);
		XA->w[16 + i] = le32dec(&databuf[0 * 128 + (16 + (i * 5 % 16)) * 4]);
		XB->w[i]      = le32dec(&databuf[1 * 128 + (i * 5 % 16) * 4]);
		XB->w[16 + i] = le32dec(&databuf[1 * 128 + (16 + (i * 5 % 16)) * 4]);
		XC->w[i]      = le32dec(&databuf[2 * 128 + (i * 5 % 16) * 4]);
		XC->w[16 + i] = le32dec(&databuf[2 * 128 + (16 + (i * 5 % 16)) * 4]);
		XD->w[i]      = le32dec(&databuf[3 * 128 + (i * 5 % 16) * 4]);
		XD->w[16 + i] = le32dec(&databuf[3 * 128 + (16 + (i * 5 % 16)) * 4]);
		XE->w[i]      = le32dec(&databuf[4 * 128 + (i * 5 % 16) * 4]);
		XE->w[16 + i] = le32dec(&databuf[4 * 128 + (16 + (i * 5 % 16)) * 4]);
		XF->w[i]      = le32dec(&databuf[5 * 128 + (i * 5 % 16) * 4]);
		XF->w[16 + i] = le32dec(&databuf[5 * 128 + (16 + (i * 5 % 16)) * 4]);
		XG->w[i]      = le32dec(&databuf[6 * 128 + (i * 5 % 16) * 4]);
		XG->w[16 + i] = le32dec(&databuf[6 * 128 + (16 + (i * 5 % 16)) * 4]);
		XH->w[i]      = le32dec(&databuf[7 * 128 + (i * 5 % 16) * 4]);
		XH->w[16 + i] = le32dec(&databuf[7 * 128 + (16 + (i * 5 % 16)) * 4]);
	}
	for (i = 0; i < 8; i++)
		dma_list[i].size = 128;

	/* 2: for i = 0 to N - 1 do */
	for (i = 0; i < 1024; i++) {
		blkcpy128(&Z[0 * 8], &XA->q[0]);
		blkcpy128(&Z[1 * 8], &XB->q[0]);
		blkcpy128(&Z[2 * 8], &XC->q[0]);
		blkcpy128(&Z[3 * 8], &XD->q[0]);
		blkcpy128(&Z[4 * 8], &XE->q[0]);
		blkcpy128(&Z[5 * 8], &XF->q[0]);
		blkcpy128(&Z[6 * 8], &XG->q[0]);
		blkcpy128(&Z[7 * 8], &XH->q[0]);
		dma_list[0].eal = mfc_ea2l(VA + i * 128);
		dma_list[1].eal = mfc_ea2l(VB + i * 128);
		dma_list[2].eal = mfc_ea2l(VC + i * 128);
		dma_list[3].eal = mfc_ea2l(VD + i * 128);
		dma_list[4].eal = mfc_ea2l(VE + i * 128);
		dma_list[5].eal = mfc_ea2l(VF + i * 128);
		dma_list[6].eal = mfc_ea2l(VG + i * 128);
		dma_list[7].eal = mfc_ea2l(VH + i * 128);
		mfc_putl(&Z[0], scratch, &dma_list[0], 8 * sizeof(mfc_list_element_t), tag1, 0, 0);
		salsa20_8_xor4(&XA->q[0], &XA->q[4], &XB->q[0], &XB->q[4], &XC->q[0], &XC->q[4], &XD->q[0], &XD->q[4]);
		salsa20_8_xor4(&XA->q[4], &XA->q[0], &XB->q[4], &XB->q[0], &XC->q[4], &XC->q[0], &XD->q[4], &XD->q[0]);
		salsa20_8_xor4(&XE->q[0], &XE->q[4], &XF->q[0], &XF->q[4], &XG->q[0], &XG->q[4], &XH->q[0], &XH->q[4]);
		salsa20_8_xor4(&XE->q[4], &XE->q[0], &XF->q[4], &XF->q[0], &XG->q[4], &XG->q[0], &XH->q[4], &XH->q[0]);
		mfc_write_tag_mask(tag_mask1);
		mfc_read_tag_status_all();
	}

	dma_list[0].eal = mfc_ea2l(VA + (XA->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	dma_list[1].eal = mfc_ea2l(VB + (XB->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	dma_list[2].eal = mfc_ea2l(VC + (XC->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	dma_list[3].eal = mfc_ea2l(VD + (XD->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	mfc_getl(&Y[0], scratch, &dma_list[0], 4 * sizeof(mfc_list_element_t), tag1, 0, 0);

	dma_list[4].eal = mfc_ea2l(VE + (XE->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	dma_list[5].eal = mfc_ea2l(VF + (XF->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	dma_list[6].eal = mfc_ea2l(VG + (XG->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	dma_list[7].eal = mfc_ea2l(VH + (XH->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
	mfc_getl(&Y[4 * 8], scratch, &dma_list[4], 4 * sizeof(mfc_list_element_t), tag2, 0, 0);

	/* 6: for i = 0 to N - 1 do */
	for (i = 0; i < 1024; i++) {
		mfc_write_tag_mask(tag_mask1);
		mfc_read_tag_status_all();
		blkxor128(XA->q, &Y[0 * 4]);
		blkxor128(XB->q, &Y[1 * 8]);
		blkxor128(XC->q, &Y[2 * 8]);
		blkxor128(XD->q, &Y[3 * 8]);
		salsa20_8_xor4(&XA->q[0], &XA->q[4], &XB->q[0], &XB->q[4], &XC->q[0], &XC->q[4], &XD->q[0], &XD->q[4]);
		salsa20_8_xor4(&XA->q[4], &XA->q[0], &XB->q[4], &XB->q[0], &XC->q[4], &XC->q[0], &XD->q[4], &XD->q[0]);

		dma_list[0].eal = mfc_ea2l(VA + (XA->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[1].eal = mfc_ea2l(VB + (XB->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[2].eal = mfc_ea2l(VC + (XC->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[3].eal = mfc_ea2l(VD + (XD->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		mfc_getl(&Y[0], scratch, &dma_list[0], 4 * sizeof(mfc_list_element_t), tag1, 0, 0);

		mfc_write_tag_mask(tag_mask2);
		mfc_read_tag_status_all();
		blkxor128(XE->q, &Y[4 * 8]);
		blkxor128(XF->q, &Y[5 * 8]);
		blkxor128(XG->q, &Y[6 * 8]);
		blkxor128(XH->q, &Y[7 * 8]);
		salsa20_8_xor4(&XE->q[0], &XE->q[4], &XF->q[0], &XF->q[4], &XG->q[0], &XG->q[4], &XH->q[0], &XH->q[4]);
		salsa20_8_xor4(&XE->q[4], &XE->q[0], &XF->q[4], &XF->q[0], &XG->q[4], &XG->q[0], &XH->q[4], &XH->q[0]);

		dma_list[4].eal = mfc_ea2l(VE + (XE->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[5].eal = mfc_ea2l(VF + (XF->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[6].eal = mfc_ea2l(VG + (XG->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[7].eal = mfc_ea2l(VH + (XH->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		mfc_getl(&Y[4 * 8], scratch, &dma_list[4], 4 * sizeof(mfc_list_element_t), tag2, 0, 0);
	}

	/* 10: B' <-- X */
	for (i = 0; i < 16; i++) {
		le32enc(&databuf[0 * 128 + (i * 5 % 16) * 4], XA->w[i]);
		le32enc(&databuf[0 * 128 + (16 + (i * 5 % 16)) * 4], XA->w[16 + i]);
		le32enc(&databuf[1 * 128 + (i * 5 % 16) * 4], XB->w[i]);
		le32enc(&databuf[1 * 128 + (16 + (i * 5 % 16)) * 4], XB->w[16 + i]);
		le32enc(&databuf[2 * 128 + (i * 5 % 16) * 4], XC->w[i]);
		le32enc(&databuf[2 * 128 + (16 + (i * 5 % 16)) * 4], XC->w[16 + i]);
		le32enc(&databuf[3 * 128 + (i * 5 % 16) * 4], XD->w[i]);
		le32enc(&databuf[3 * 128 + (16 + (i * 5 % 16)) * 4], XD->w[16 + i]);
		le32enc(&databuf[4 * 128 + (i * 5 % 16) * 4], XE->w[i]);
		le32enc(&databuf[4 * 128 + (16 + (i * 5 % 16)) * 4], XE->w[16 + i]);
		le32enc(&databuf[5 * 128 + (i * 5 % 16) * 4], XF->w[i]);
		le32enc(&databuf[5 * 128 + (16 + (i * 5 % 16)) * 4], XF->w[16 + i]);
		le32enc(&databuf[6 * 128 + (i * 5 % 16) * 4], XG->w[i]);
		le32enc(&databuf[6 * 128 + (16 + (i * 5 % 16)) * 4], XG->w[16 + i]);
		le32enc(&databuf[7 * 128 + (i * 5 % 16) * 4], XH->w[i]);
		le32enc(&databuf[7 * 128 + (16 + (i * 5 % 16)) * 4], XH->w[16 + i]);
	}
}

static void
scrypt_1024_1_1_256_sp8(const unsigned char * input1,
                        unsigned char       * output1,
                        const unsigned char * input2,
                        unsigned char       * output2,
                        const unsigned char * input3,
                        unsigned char       * output3,
                        const unsigned char * input4,
                        unsigned char       * output4,
                        const unsigned char * input5,
                        unsigned char       * output5,
                        const unsigned char * input6,
                        unsigned char       * output6,
                        const unsigned char * input7,
                        unsigned char       * output7,
                        const unsigned char * input8,
                        unsigned char       * output8,
                        uint64_t              scratchpad)
{
	static uint8_t databuf[128 * 8] __attribute__((aligned(128)));
	uint8_t * B1, * B2, * B3, * B4, * B5, * B6, * B7, * B8;

	const uint32_t r = 1;
	const uint32_t p = 1;

	B1 = databuf;
	B2 = databuf + 128 * 1;
	B3 = databuf + 128 * 2;
	B4 = databuf + 128 * 3;
	B5 = databuf + 128 * 4;
	B6 = databuf + 128 * 5;
	B7 = databuf + 128 * 6;
	B8 = databuf + 128 * 7;

	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input1, 80, (const uint8_t*)input1, 80, 1, B1, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input2, 80, (const uint8_t*)input2, 80, 1, B2, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input3, 80, (const uint8_t*)input3, 80, 1, B3, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input4, 80, (const uint8_t*)input4, 80, 1, B4, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input5, 80, (const uint8_t*)input5, 80, 1, B5, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input6, 80, (const uint8_t*)input6, 80, 1, B6, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input7, 80, (const uint8_t*)input7, 80, 1, B7, p * 128 * r);
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256((const uint8_t*)input8, 80, (const uint8_t*)input8, 80, 1, B8, p * 128 * r);

	scrypt_spu_core8(databuf, scratchpad);

	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input1, 80, B1, p * 128 * r, 1, (uint8_t*)output1, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input2, 80, B2, p * 128 * r, 1, (uint8_t*)output2, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input3, 80, B3, p * 128 * r, 1, (uint8_t*)output3, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input4, 80, B4, p * 128 * r, 1, (uint8_t*)output4, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input5, 80, B5, p * 128 * r, 1, (uint8_t*)output5, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input6, 80, B6, p * 128 * r, 1, (uint8_t*)output6, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input7, 80, B7, p * 128 * r, 1, (uint8_t*)output7, 32);
	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
	PBKDF2_SHA256((const uint8_t*)input8, 80, B8, p * 128 * r, 1, (uint8_t*)output8, 32);
}

static int
scanhash_scrypt(uint64_t work_restart_ptr, unsigned char *pdata,
	uint64_t scratchbuf, const unsigned char *ptarget,
	uint32_t max_nonce, uint32_t *hashes_done)
{
	unsigned char data1[80];
	unsigned char tmp_hash1[32];
	unsigned char data2[80];
	unsigned char tmp_hash2[32];
	unsigned char data3[80];
	unsigned char tmp_hash3[32];
	unsigned char data4[80];
	unsigned char tmp_hash4[32];
	unsigned char data5[80];
	unsigned char tmp_hash5[32];
	unsigned char data6[80];
	unsigned char tmp_hash6[32];
	unsigned char data7[80];
	unsigned char tmp_hash7[32];
	unsigned char data8[80];
	unsigned char tmp_hash8[32];
	uint32_t *nonce1 = (uint32_t *)(data1 + 64 + 12);
	uint32_t *nonce2 = (uint32_t *)(data2 + 64 + 12);
	uint32_t *nonce3 = (uint32_t *)(data3 + 64 + 12);
	uint32_t *nonce4 = (uint32_t *)(data4 + 64 + 12);
	uint32_t *nonce5 = (uint32_t *)(data5 + 64 + 12);
	uint32_t *nonce6 = (uint32_t *)(data6 + 64 + 12);
	uint32_t *nonce7 = (uint32_t *)(data7 + 64 + 12);
	uint32_t *nonce8 = (uint32_t *)(data8 + 64 + 12);
	uint32_t n = 0;
	uint32_t Htarg = le32dec(ptarget + 28);
	int i;
	int tag3 = 3, tag_mask3 = 1 << tag3;
	int work_restart = 0;

	for (i = 0; i < 80/4; i++) {
		((uint32_t *)data1)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
		((uint32_t *)data2)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
		((uint32_t *)data3)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
		((uint32_t *)data4)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
		((uint32_t *)data5)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
		((uint32_t *)data6)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
		((uint32_t *)data7)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
		((uint32_t *)data8)[i] = __builtin_bswap32(((uint32_t *)pdata)[i]);
	}
	
	while(1) {
		/* request 'work_restart[thr_id].restart' from external memory */
		mfc_get(&work_restart, work_restart_ptr, 4, tag3, 0, 0);

		le32enc(nonce1, n + 1);
		le32enc(nonce2, n + 2);
		le32enc(nonce3, n + 3);
		le32enc(nonce4, n + 4);
		le32enc(nonce5, n + 5);
		le32enc(nonce6, n + 6);
		le32enc(nonce7, n + 7);
		le32enc(nonce8, n + 8);
		scrypt_1024_1_1_256_sp8(data1, tmp_hash1, data2, tmp_hash2,
		                        data3, tmp_hash3, data4, tmp_hash4,
		                        data5, tmp_hash5, data6, tmp_hash6,
		                        data7, tmp_hash7, data8, tmp_hash8,
		                        scratchbuf);

		if (le32dec(tmp_hash1+28) <= Htarg) {
			be32enc(pdata + 64 + 12, n + 1);
			*hashes_done = n;
			return true;
		}

		if (le32dec(tmp_hash2+28) <= Htarg && n + 2 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 2);
			*hashes_done = n + 2;
			return true;
		}

		if (le32dec(tmp_hash3+28) <= Htarg && n + 3 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 3);
			*hashes_done = n + 3;
			return true;
		}

		if (le32dec(tmp_hash4+28) <= Htarg && n + 4 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 4);
			*hashes_done = n + 4;
			return true;
		}

		if (le32dec(tmp_hash5+28) <= Htarg && n + 5 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 5);
			*hashes_done = n + 5;
			return true;
		}

		if (le32dec(tmp_hash6+28) <= Htarg && n + 6 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 6);
			*hashes_done = n + 6;
			return true;
		}

		if (le32dec(tmp_hash7+28) <= Htarg && n + 7 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 7);
			*hashes_done = n + 7;
			return true;
		}

		if (le32dec(tmp_hash8+28) <= Htarg && n + 8 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 8);
			*hashes_done = n + 8;
			return true;
		}

		n += 8;

		if (n >= max_nonce) {
			*hashes_done = max_nonce;
			break;
		}

		/* ensure that 'work_restart[thr_id].restart' has been read */
		mfc_write_tag_mask(tag_mask3);
		mfc_read_tag_status_all();

		if (work_restart) {
			*hashes_done = n;
			break;
		}
	}
	return false;
}

int main(uint64_t spe_id, uint64_t argp, uint64_t envp)
{
	static scanhash_spu_args args __attribute__((aligned(16)));
	int tag = 1, tag_mask = 1 << tag;
	int rc;

	mfc_get(&args, argp, sizeof(args), tag, 0, 0);
	mfc_write_tag_mask(tag_mask);
	mfc_read_tag_status_all();

	rc = scanhash_scrypt(envp, args.data, argp + 1024,
			    args.target, args.max_nonce,
			    &args.hashes_done);

	mfc_put(&args, argp, sizeof(args), tag, 0, 0);
	mfc_write_tag_mask(tag_mask);
	mfc_read_tag_status_all();

	return rc;
}
