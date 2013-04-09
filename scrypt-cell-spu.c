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

static inline __attribute__((always_inline)) void
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

void salsa20_8_xor4x_asm(uint32x4 * data);

void scrypt_spu_loop1_asm(uint32x4 * data,
                             uint32x4 * dma_vect_list,
                             uint32x4   dma_vect_step,
                             uint64_t   scratch_eahi,
                             int        tag1,
                             int        tag_mask1,
                             int        tag2,
                             int        tag_mask2);

static inline __attribute__((always_inline)) void
salsa20_8_xor4d(uint32x4 * data)
{
	salsa20_8_xor4(&data[0],  &data[4],  &data[8],  &data[12],
	               &data[16], &data[20], &data[24], &data[28]);
	salsa20_8_xor4(&data[4],  &data[0],  &data[12], &data[8],
	               &data[20], &data[16], &data[28], &data[24]);
}

static mfc_list_element_t dma_list[8] __attribute__((aligned(128)));

void scrypt_spu_loop1(uint32x4 * data,
                      uint32x4 * dma_vect_list,
                      uint32x4   dma_vect_step,
                      uint64_t   scratch_eahi,
                      int        tag1,
                      int        tag_mask1,
                      int        tag2,
                      int        tag_mask2)
{
	static uint32x4 Z[8 * 8] __attribute__((aligned(128)));
	int i;

	blkcpy128(&Z[0 * 8], &data[0 * 8]);
	blkcpy128(&Z[1 * 8], &data[1 * 8]);
	blkcpy128(&Z[2 * 8], &data[2 * 8]);
	blkcpy128(&Z[3 * 8], &data[3 * 8]);
	spu_dsync();
	spu_mfcdma64(&Z[0], scratch_eahi, (uint32_t)&dma_vect_list[0], 4 * 8, tag1, MFC_PUTL_CMD);
	for (i = 0; i < 1023; i++) {
		salsa20_8_xor4d(data);
		spu_writech(MFC_WrTagMask, tag_mask2);
		spu_mfcstat(MFC_TAG_UPDATE_ALL);
		dma_vect_list[2] += dma_vect_step;
		dma_vect_list[3] += dma_vect_step;
		blkcpy128(&Z[4 * 8], &data[4 * 8]);
		blkcpy128(&Z[5 * 8], &data[5 * 8]);
		blkcpy128(&Z[6 * 8], &data[6 * 8]);
		blkcpy128(&Z[7 * 8], &data[7 * 8]);
		spu_dsync();
		spu_mfcdma64(&Z[4 * 8], scratch_eahi, (uint32_t)&dma_vect_list[2], 4 * 8, tag2, MFC_PUTL_CMD);

		salsa20_8_xor4d(data + 32);
		spu_writech(MFC_WrTagMask, tag_mask1);
		spu_mfcstat(MFC_TAG_UPDATE_ALL);
		dma_vect_list[0] += dma_vect_step;
		dma_vect_list[1] += dma_vect_step;
		blkcpy128(&Z[0 * 8], &data[0 * 8]);
		blkcpy128(&Z[1 * 8], &data[1 * 8]);
		blkcpy128(&Z[2 * 8], &data[2 * 8]);
		blkcpy128(&Z[3 * 8], &data[3 * 8]);
		spu_dsync();
		spu_mfcdma64(&Z[0], scratch_eahi, (uint32_t)&dma_vect_list[0], 4 * 8, tag1, MFC_PUTL_CMD);
	}
	salsa20_8_xor4d(data);
	spu_writech(MFC_WrTagMask, tag_mask2);
	spu_mfcstat(MFC_TAG_UPDATE_ALL);
	dma_vect_list[2] += dma_vect_step;
	dma_vect_list[3] += dma_vect_step;
	blkcpy128(&Z[4 * 8], &data[4 * 8]);
	blkcpy128(&Z[5 * 8], &data[5 * 8]);
	blkcpy128(&Z[6 * 8], &data[6 * 8]);
	blkcpy128(&Z[7 * 8], &data[7 * 8]);
	spu_dsync();
	spu_mfcdma64(&Z[4 * 8], scratch_eahi, (uint32_t)&dma_vect_list[2], 4 * 8, tag2, MFC_PUTL_CMD);
	salsa20_8_xor4d(data + 32);

	spu_writech(MFC_WrTagMask, tag_mask1 | tag_mask2);
	spu_mfcstat(MFC_TAG_UPDATE_ALL);
}

/* Use assembly implementation */
#define scrypt_spu_loop1 scrypt_spu_loop1_asm

static void
scrypt_spu_core8(uint32_t *databuf32, uint64_t scratch)
{
	static XY X[8] __attribute__((aligned(128)));
	static uint32x4 Y[8 * 8] __attribute__((aligned(128)));
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
		XA->w[i]      = databuf32[0 * 32 + (i * 5 % 16)];
		XA->w[16 + i] = databuf32[0 * 32 + (16 + (i * 5 % 16))];
		XB->w[i]      = databuf32[1 * 32 + (i * 5 % 16)];
		XB->w[16 + i] = databuf32[1 * 32 + (16 + (i * 5 % 16))];
		XC->w[i]      = databuf32[2 * 32 + (i * 5 % 16)];
		XC->w[16 + i] = databuf32[2 * 32 + (16 + (i * 5 % 16))];
		XD->w[i]      = databuf32[3 * 32 + (i * 5 % 16)];
		XD->w[16 + i] = databuf32[3 * 32 + (16 + (i * 5 % 16))];
		XE->w[i]      = databuf32[4 * 32 + (i * 5 % 16)];
		XE->w[16 + i] = databuf32[4 * 32 + (16 + (i * 5 % 16))];
		XF->w[i]      = databuf32[5 * 32 + (i * 5 % 16)];
		XF->w[16 + i] = databuf32[5 * 32 + (16 + (i * 5 % 16))];
		XG->w[i]      = databuf32[6 * 32 + (i * 5 % 16)];
		XG->w[16 + i] = databuf32[6 * 32 + (16 + (i * 5 % 16))];
		XH->w[i]      = databuf32[7 * 32 + (i * 5 % 16)];
		XH->w[16 + i] = databuf32[7 * 32 + (16 + (i * 5 % 16))];
	}
	for (i = 0; i < 8; i++)
		dma_list[i].size = 128;

	/* 2: for i = 0 to N - 1 do */
	do {
		uint32x4 dma_vect_list[4] = {
			{
				128, mfc_ea2l(scratch + 128 * 1024 * 0),
				128, mfc_ea2l(scratch + 128 * 1024 * 1)
			},
			{
				128, mfc_ea2l(scratch + 128 * 1024 * 2),
				128, mfc_ea2l(scratch + 128 * 1024 * 3)
			},
			{
				128, mfc_ea2l(scratch + 128 * 1024 * 4) - 128,
				128, mfc_ea2l(scratch + 128 * 1024 * 5) - 128
			},
			{
				128, mfc_ea2l(scratch + 128 * 1024 * 6) - 128,
				128, mfc_ea2l(scratch + 128 * 1024 * 7) - 128
			}
		};
		uint32x4 dma_vect_step = { 0, 128, 0, 128 };
		uint32_t scratch_eahi = mfc_ea2h(scratch);
		scrypt_spu_loop1((uint32x4 *)XA, dma_vect_list, dma_vect_step, scratch_eahi,
				  tag1, tag_mask1, tag2, tag_mask2);
	} while (0);

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
		salsa20_8_xor4d(&XA->q[0]);

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
		salsa20_8_xor4d(&XE->q[0]);

		dma_list[4].eal = mfc_ea2l(VE + (XE->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[5].eal = mfc_ea2l(VF + (XF->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[6].eal = mfc_ea2l(VG + (XG->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		dma_list[7].eal = mfc_ea2l(VH + (XH->w[16] & 1023) * 128); /* j <-- Integerify(X) mod N */
		mfc_getl(&Y[4 * 8], scratch, &dma_list[4], 4 * sizeof(mfc_list_element_t), tag2, 0, 0);
	}

	/* 10: B' <-- X */
	for (i = 0; i < 16; i++) {
		databuf32[0 * 32 + (i * 5 % 16)] = XA->w[i];
		databuf32[0 * 32 + (16 + (i * 5 % 16))] = XA->w[16 + i];
		databuf32[1 * 32 + (i * 5 % 16)] = XB->w[i];
		databuf32[1 * 32 + (16 + (i * 5 % 16))] = XB->w[16 + i];
		databuf32[2 * 32 + (i * 5 % 16)] = XC->w[i];
		databuf32[2 * 32 + (16 + (i * 5 % 16))] = XC->w[16 + i];
		databuf32[3 * 32 + (i * 5 % 16)] = XD->w[i];
		databuf32[3 * 32 + (16 + (i * 5 % 16))] = XD->w[16 + i];
		databuf32[4 * 32 + (i * 5 % 16)] = XE->w[i];
		databuf32[4 * 32 + (16 + (i * 5 % 16))] = XE->w[16 + i];
		databuf32[5 * 32 + (i * 5 % 16)] = XF->w[i];
		databuf32[5 * 32 + (16 + (i * 5 % 16))] = XF->w[16 + i];
		databuf32[6 * 32 + (i * 5 % 16)] = XG->w[i];
		databuf32[6 * 32 + (16 + (i * 5 % 16))] = XG->w[16 + i];
		databuf32[7 * 32 + (i * 5 % 16)] = XH->w[i];
		databuf32[7 * 32 + (16 + (i * 5 % 16))] = XH->w[16 + i];
	}
}

static void
scrypt_1024_1_1_256_sp8(const uint32_t * input1,
                        uint32_t       * output1,
                        const uint32_t * input2,
                        uint32_t       * output2,
                        const uint32_t * input3,
                        uint32_t       * output3,
                        const uint32_t * input4,
                        uint32_t       * output4,
                        const uint32_t * input5,
                        uint32_t       * output5,
                        const uint32_t * input6,
                        uint32_t       * output6,
                        const uint32_t * input7,
                        uint32_t       * output7,
                        const uint32_t * input8,
                        uint32_t       * output8,
                        uint64_t              scratchpad)
{
	uint32_t tstate1[8], tstate2[8], tstate3[8], tstate4[8];
	uint32_t tstate5[8], tstate6[8], tstate7[8], tstate8[8];

	uint32_t ostate1[8], ostate2[8], ostate3[8], ostate4[8];
	uint32_t ostate5[8], ostate6[8], ostate7[8], ostate8[8];
	
	static uint32_t databuf[32 * 8] __attribute__((aligned(128)));
	uint32_t * B1, * B2, * B3, * B4, * B5, * B6, * B7, * B8;

	B1 = databuf;
	B2 = databuf + 32 * 1;
	B3 = databuf + 32 * 2;
	B4 = databuf + 32 * 3;
	B5 = databuf + 32 * 4;
	B6 = databuf + 32 * 5;
	B7 = databuf + 32 * 6;
	B8 = databuf + 32 * 7;

	PBKDF2_SHA256_80_128_init(input1, tstate1, ostate1);
	PBKDF2_SHA256_80_128_init(input2, tstate2, ostate2);
	PBKDF2_SHA256_80_128_init(input3, tstate3, ostate3);
	PBKDF2_SHA256_80_128_init(input4, tstate4, ostate4);
	PBKDF2_SHA256_80_128_init(input5, tstate5, ostate5);
	PBKDF2_SHA256_80_128_init(input6, tstate6, ostate6);
	PBKDF2_SHA256_80_128_init(input7, tstate7, ostate7);
	PBKDF2_SHA256_80_128_init(input8, tstate8, ostate8);
	PBKDF2_SHA256_80_128(tstate1, ostate1, input1, B1);
	PBKDF2_SHA256_80_128(tstate2, ostate2, input2, B2);
	PBKDF2_SHA256_80_128(tstate3, ostate3, input3, B3);
	PBKDF2_SHA256_80_128(tstate4, ostate4, input4, B4);
	PBKDF2_SHA256_80_128(tstate5, ostate5, input5, B5);
	PBKDF2_SHA256_80_128(tstate6, ostate6, input6, B6);
	PBKDF2_SHA256_80_128(tstate7, ostate7, input7, B7);
	PBKDF2_SHA256_80_128(tstate8, ostate8, input8, B8);

	scrypt_spu_core8(databuf, scratchpad);

	PBKDF2_SHA256_80_128_32(tstate1, ostate1, input1, B1, output1);
	PBKDF2_SHA256_80_128_32(tstate2, ostate2, input2, B2, output2);
	PBKDF2_SHA256_80_128_32(tstate3, ostate3, input3, B3, output3);
	PBKDF2_SHA256_80_128_32(tstate4, ostate4, input4, B4, output4);
	PBKDF2_SHA256_80_128_32(tstate5, ostate5, input5, B5, output5);
	PBKDF2_SHA256_80_128_32(tstate6, ostate6, input6, B6, output6);
	PBKDF2_SHA256_80_128_32(tstate7, ostate7, input7, B7, output7);
	PBKDF2_SHA256_80_128_32(tstate8, ostate8, input8, B8, output8);
}

static int
scanhash_scrypt(uint64_t work_restart_ptr, unsigned char *pdata,
	uint64_t scratchbuf, const unsigned char *ptarget,
	uint32_t max_nonce, uint32_t *hashes_done)
{
	uint32_t data1[20], tmp_hash1[8];
	uint32_t data2[20], tmp_hash2[8];
	uint32_t data3[20], tmp_hash3[8];
	uint32_t data4[20], tmp_hash4[8];
	uint32_t data5[20], tmp_hash5[8];
	uint32_t data6[20], tmp_hash6[8];
	uint32_t data7[20], tmp_hash7[8];
	uint32_t data8[20], tmp_hash8[8];
	uint32_t *nonce1 = &data1[19];
	uint32_t *nonce2 = &data2[19];
	uint32_t *nonce3 = &data3[19];
	uint32_t *nonce4 = &data4[19];
	uint32_t *nonce5 = &data5[19];
	uint32_t *nonce6 = &data6[19];
	uint32_t *nonce7 = &data7[19];
	uint32_t *nonce8 = &data8[19];
	uint32_t n = 0;
	uint32_t Htarg = le32dec(ptarget + 28);
	int i;
	int tag3 = 3, tag_mask3 = 1 << tag3;
	int work_restart = 0;

	for (i = 0; i < 80/4; i++) {
		data1[i] = be32dec(&((uint32_t *)pdata)[i]);
		data2[i] = be32dec(&((uint32_t *)pdata)[i]);
		data3[i] = be32dec(&((uint32_t *)pdata)[i]);
		data4[i] = be32dec(&((uint32_t *)pdata)[i]);
		data5[i] = be32dec(&((uint32_t *)pdata)[i]);
		data6[i] = be32dec(&((uint32_t *)pdata)[i]);
		data7[i] = be32dec(&((uint32_t *)pdata)[i]);
		data8[i] = be32dec(&((uint32_t *)pdata)[i]);
	}
	
	while(1) {
		/* request 'work_restart[thr_id].restart' from external memory */
		mfc_get(&work_restart, work_restart_ptr, 4, tag3, 0, 0);

		*nonce1 = n + 1;
		*nonce2 = n + 2;
		*nonce3 = n + 3;
		*nonce4 = n + 4;
		*nonce5 = n + 5;
		*nonce6 = n + 6;
		*nonce7 = n + 7;
		*nonce8 = n + 8;
		scrypt_1024_1_1_256_sp8(data1, tmp_hash1, data2, tmp_hash2,
		                        data3, tmp_hash3, data4, tmp_hash4,
		                        data5, tmp_hash5, data6, tmp_hash6,
		                        data7, tmp_hash7, data8, tmp_hash8,
		                        scratchbuf);

		if (tmp_hash1[7] <= Htarg) {
			be32enc(pdata + 64 + 12, n + 1);
			*hashes_done = n;
			return true;
		}

		if (tmp_hash2[7] <= Htarg && n + 2 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 2);
			*hashes_done = n + 2;
			return true;
		}

		if (tmp_hash3[7] <= Htarg && n + 3 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 3);
			*hashes_done = n + 3;
			return true;
		}

		if (tmp_hash4[7] <= Htarg && n + 4 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 4);
			*hashes_done = n + 4;
			return true;
		}

		if (tmp_hash5[7] <= Htarg && n + 5 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 5);
			*hashes_done = n + 5;
			return true;
		}

		if (tmp_hash6[7] <= Htarg && n + 6 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 6);
			*hashes_done = n + 6;
			return true;
		}

		if (tmp_hash7[7] <= Htarg && n + 7 <= max_nonce) {
			be32enc(pdata + 64 + 12, n + 7);
			*hashes_done = n + 7;
			return true;
		}

		if (tmp_hash8[7] <= Htarg && n + 8 <= max_nonce) {
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
