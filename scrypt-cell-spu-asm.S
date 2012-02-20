/*-
 * Copyright 2012 Siarhei Siamashka
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
 */

.text
.global scrypt_spu_loop1_asm

/*****************************************************************************/

.balign 16
shufmask3012:
	.byte	12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
shufmask2301:
	.byte	8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7
shufmask1230:
	.byte	4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3

/*****************************************************************************/

.balign 16
registers_save_area:
.rept (128 - 80) * 16
	.byte	0
.endr

.macro save_regs start_reg=80, end_reg=127
	stqr	$\start_reg,	registers_save_area + (\start_reg - 80) * 16
.if \start_reg < \end_reg
	save_regs "(\start_reg + 1)", \end_reg
.endif
.endm

.macro restore_regs start_reg=80, end_reg=127
	lqr	$\start_reg,	registers_save_area + (\start_reg - 80) * 16
.if \start_reg < \end_reg
	restore_regs "(\start_reg + 1)", \end_reg
.endif
.endm

/*****************************************************************************/

#define MFC_PUTL_CMD 36
#define MFC_TAG_UPDATE_ALL 2

/*
 * dual-issue for all shufb instructions
 */
.macro salsa20_8_step	X0s, X1s, X2s, X3s, /* 16 regs with data */ \
			Y0s, Y1s, Y2s, Y3s,                         \
			Z0s, Z1s, Z2s, Z3s,                         \
			W0s, W1s, W2s, W3s,                         \
			X0,  X1,  X2,  X3,  /* 16 regs with data */ \
			Y0,  Y1,  Y2,  Y3,                          \
			Z0,  Z1,  Z2,  Z3,                          \
			W0,  W1,  W2,  W3,                          \
			TX,  TY,  TZ,  TW,  /* 16 temporary regs */ \
			X1t, X2t, X3t,                              \
			Y1t, Y2t, Y3t,                              \
			Z1t, Z2t, Z3t,                              \
			W1t, W2t, W3t,                              \
			MASK3012,           /* shuffle constants */ \
			MASK2301,                                   \
			MASK1230

	a	\TX,	\X0s,	\X3s
	a	\TY,	\Y0s,	\Y3s
	a	\TZ,	\Z0s,	\Z3s
	a	\TW,	\W0s,	\W3s
	roti	\TX,	\TX,	7
	roti	\TY,	\TY,	7
	roti	\TZ,	\TZ,	7
	roti	\TW,	\TW,	7
	xor	\X1,	\X1s,	\TX
	xor	\Y1,	\Y1s,	\TY
	xor	\Z1,	\Z1s,	\TZ
	xor	\W1,	\W1s,	\TW
	a	\TX,	\X1,	\X0s
					shufb	\X1t,	\X1,	\X1, \MASK3012
	a	\TY,	\Y1,	\Y0s
					shufb	\Y1t,	\Y1,	\Y1, \MASK3012
	a	\TZ,	\Z1,	\Z0s
					shufb	\Z1t,	\Z1,	\Z1, \MASK3012
	a	\TW,	\W1,	\W0s
					shufb	\W1t,	\W1,	\W1, \MASK3012
	roti	\TX,	\TX,	9
	roti	\TY,	\TY,	9
	roti	\TZ,	\TZ,	9
	roti	\TW,	\TW,	9
	xor	\X2,	\X2s,	\TX
	xor	\Y2,	\Y2s,	\TY
	xor	\Z2,	\Z2s,	\TZ
	xor	\W2,	\W2s,	\TW
	a	\TX,	\X2,	\X1
					shufb	\X2t,	\X2,	\X2, \MASK2301
	a	\TY,	\Y2,	\Y1
					shufb	\Y2t,	\Y2,	\Y2, \MASK2301
	a	\TZ,	\Z2,	\Z1
					shufb	\Z2t,	\Z2,	\Z2, \MASK2301
	a	\TW,	\W2,	\W1
					shufb	\W2t,	\W2,	\W2, \MASK2301
	roti	\TX,	\TX,	13
	roti	\TY,	\TY,	13
	roti	\TZ,	\TZ,	13
	roti	\TW,	\TW,	13
	xor	\X3,	\X3s,	\TX
	xor	\Y3,	\Y3s,	\TY
	xor	\Z3,	\Z3s,	\TZ
	xor	\W3,	\W3s,	\TW
	a	\TX,	\X3,	\X2
					shufb	\X3t,	\X3,	\X3, \MASK1230
	a	\TY,	\Y3,	\Y2
					shufb	\Y3t,	\Y3,	\Y3, \MASK1230
	a	\TZ,	\Z3,	\Z2
					shufb	\Z3t,	\Z3,	\Z3, \MASK1230
	a	\TW,	\W3,	\W2
					shufb	\W3t,	\W3,	\W3, \MASK1230
	roti	\TX,	\TX,	18
	roti	\TY,	\TY,	18
	roti	\TZ,	\TZ,	18
	roti	\TW,	\TW,	18
	xor	\X0,	\X0s,	\TX
	xor	\Y0,	\Y0s,	\TY
	xor	\Z0,	\Z0s,	\TZ
	xor	\W0,	\W0s,	\TW

	a	\TX,	\X0,	\X1t
	a	\TY,	\Y0,	\Y1t
	a	\TZ,	\Z0,	\Z1t
	a	\TW,	\W0,	\W1t
	roti	\TX,	\TX,	7
	roti	\TY,	\TY,	7
	roti	\TZ,	\TZ,	7
	roti	\TW,	\TW,	7
	xor	\X3t,	\X3t,	\TX
	xor	\Y3t,	\Y3t,	\TY
	xor	\Z3t,	\Z3t,	\TZ
	xor	\W3t,	\W3t,	\TW
	a	\TX,	\X3t,	\X0
					shufb	\X3,	\X3t,	\X3t, \MASK3012
	a	\TY,	\Y3t,	\Y0
					shufb	\Y3,	\Y3t,	\Y3t, \MASK3012
	a	\TZ,	\Z3t,	\Z0
					shufb	\Z3,	\Z3t,	\Z3t, \MASK3012
	a	\TW,	\W3t,	\W0
					shufb	\W3,	\W3t,	\W3t, \MASK3012
	roti	\TX,	\TX,	9
	roti	\TY,	\TY,	9
	roti	\TZ,	\TZ,	9
	roti	\TW,	\TW,	9
	xor	\X2t,	\X2t,	\TX
	xor	\Y2t,	\Y2t,	\TY
	xor	\Z2t,	\Z2t,	\TZ
	xor	\W2t,	\W2t,	\TW
	a	\TX,	\X2t,	\X3t
					shufb	\X2,	\X2t,	\X2t, \MASK2301
	a	\TY,	\Y2t,	\Y3t
					shufb	\Y2,	\Y2t,	\Y2t, \MASK2301
	a	\TZ,	\Z2t,	\Z3t
					shufb	\Z2,	\Z2t,	\Z2t, \MASK2301
	a	\TW,	\W2t,	\W3t
					shufb	\W2,	\W2t,	\W2t, \MASK2301
	roti	\TX,	\TX,	13
	roti	\TY,	\TY,	13
	roti	\TZ,	\TZ,	13
	roti	\TW,	\TW,	13
	xor	\X1t,	\X1t,	\TX
	xor	\Y1t,	\Y1t,	\TY
	xor	\Z1t,	\Z1t,	\TZ
	xor	\W1t,	\W1t,	\TW
	a	\TX,	\X1t,	\X2t
					shufb	\X1,	\X1t,	\X1t, \MASK1230
	a	\TY,	\Y1t,	\Y2t
					shufb	\Y1,	\Y1t,	\Y1t, \MASK1230
	a	\TZ,	\Z1t,	\Z2t
					shufb	\Z1,	\Z1t,	\Z1t, \MASK1230
	a	\TW,	\W1t,	\W2t
					shufb	\W1,	\W1t,	\W1t, \MASK1230
	roti	\TX,	\TX,	18
	roti	\TY,	\TY,	18
	roti	\TZ,	\TZ,	18
	roti	\TW,	\TW,	18
	xor	\X0,	\X0,	\TX
	xor	\Y0,	\Y0,	\TY
	xor	\Z0,	\Z0,	\TZ
	xor	\W0,	\W0,	\TW
.endm

.macro salsa20_8_xor4d	X0l, X1l, X2l, X3l, \
			Y0l, Y1l, Y2l, Y3l, \
			Z0l, Z1l, Z2l, Z3l, \
			W0l, W1l, W2l, W3l, \
			X0r, X1r, X2r, X3r, \
			Y0r, Y1r, Y2r, Y3r, \
			Z0r, Z1r, Z2r, Z3r, \
			W0r, W1r, W2r, W3r, \
			X0c, X1c, X2c, X3c, \
			Y0c, Y1c, Y2c, Y3c, \
			Z0c, Z1c, Z2c, Z3c, \
			W0c, W1c, W2c, W3c, \
			TX,  TY,  TZ,  TW,  \
			X1t, X2t, X3t,      \
			Y1t, Y2t, Y3t,      \
			Z1t, Z2t, Z3t,      \
			W1t, W2t, W3t,      \
			MASK3012,           \
			MASK2301,           \
			MASK1230

	xor	\X0c,	\X0l,	\X0r
	xor	\X1c,	\X1l,	\X1r
	xor	\X2c,	\X2l,	\X2r
	xor	\X3c,	\X3l,	\X3r
	xor	\Y0c,	\Y0l,	\Y0r
	xor	\Y1c,	\Y1l,	\Y1r
	xor	\Y2c,	\Y2l,	\Y2r
	xor	\Y3c,	\Y3l,	\Y3r
	xor	\Z0c,	\Z0l,	\Z0r
	xor	\Z1c,	\Z1l,	\Z1r
	xor	\Z2c,	\Z2l,	\Z2r
	xor	\Z3c,	\Z3l,	\Z3r
	xor	\W0c,	\W0l,	\W0r
	xor	\W1c,	\W1l,	\W1r
	xor	\W2c,	\W2l,	\W2r
	xor	\W3c,	\W3l,	\W3r

.balign 8
	salsa20_8_step \
		\X0c, \X1c, \X2c, \X3c, \
		\Y0c, \Y1c, \Y2c, \Y3c, \
		\Z0c, \Z1c, \Z2c, \Z3c, \
		\W0c, \W1c, \W2c, \W3c, \
		\X0l, \X1l, \X2l, \X3l, \
		\Y0l, \Y1l, \Y2l, \Y3l, \
		\Z0l, \Z1l, \Z2l, \Z3l, \
		\W0l, \W1l, \W2l, \W3l, \
		\TX,  \TY,  \TZ,  \TW,  \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230

.balign 8
.rept 3
	salsa20_8_step \
		\X0l, \X1l, \X2l, \X3l, \
		\Y0l, \Y1l, \Y2l, \Y3l, \
		\Z0l, \Z1l, \Z2l, \Z3l, \
		\W0l, \W1l, \W2l, \W3l, \
		\X0l, \X1l, \X2l, \X3l, \
		\Y0l, \Y1l, \Y2l, \Y3l, \
		\Z0l, \Z1l, \Z2l, \Z3l, \
		\W0l, \W1l, \W2l, \W3l, \
		\TX,  \TY,  \TZ,  \TW, \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230
.endr

	a	\X0l, \X0l, \X0c
	a	\X1l, \X1l, \X1c
	a	\X2l, \X2l, \X2c
	a	\X3l, \X3l, \X3c
	a	\Y0l, \Y0l, \Y0c
	a	\Y1l, \Y1l, \Y1c
	a	\Y2l, \Y2l, \Y2c
	a	\Y3l, \Y3l, \Y3c
	a	\Z0l, \Z0l, \Z0c
	a	\Z1l, \Z1l, \Z1c
	a	\Z2l, \Z2l, \Z2c
	a	\Z3l, \Z3l, \Z3c
	a	\W0l, \W0l, \W0c
	a	\W1l, \W1l, \W1c
	a	\W2l, \W2l, \W2c
	a	\W3l, \W3l, \W3c

	xor	\X0c,	\X0l,	\X0r
	xor	\X1c,	\X1l,	\X1r
	xor	\X2c,	\X2l,	\X2r
	xor	\X3c,	\X3l,	\X3r
	xor	\Y0c,	\Y0l,	\Y0r
	xor	\Y1c,	\Y1l,	\Y1r
	xor	\Y2c,	\Y2l,	\Y2r
	xor	\Y3c,	\Y3l,	\Y3r
	xor	\Z0c,	\Z0l,	\Z0r
	xor	\Z1c,	\Z1l,	\Z1r
	xor	\Z2c,	\Z2l,	\Z2r
	xor	\Z3c,	\Z3l,	\Z3r
	xor	\W0c,	\W0l,	\W0r
	xor	\W1c,	\W1l,	\W1r
	xor	\W2c,	\W2l,	\W2r
	xor	\W3c,	\W3l,	\W3r

.balign 8
	salsa20_8_step \
		\X0c, \X1c, \X2c, \X3c, \
		\Y0c, \Y1c, \Y2c, \Y3c, \
		\Z0c, \Z1c, \Z2c, \Z3c, \
		\W0c, \W1c, \W2c, \W3c, \
		\X0r, \X1r, \X2r, \X3r, \
		\Y0r, \Y1r, \Y2r, \Y3r, \
		\Z0r, \Z1r, \Z2r, \Z3r, \
		\W0r, \W1r, \W2r, \W3r, \
		\TX,  \TY,  \TZ,  \TW,  \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230

.balign 8
.rept 3
	salsa20_8_step \
		\X0r, \X1r, \X2r, \X3r, \
		\Y0r, \Y1r, \Y2r, \Y3r, \
		\Z0r, \Z1r, \Z2r, \Z3r, \
		\W0r, \W1r, \W2r, \W3r, \
		\X0r, \X1r, \X2r, \X3r, \
		\Y0r, \Y1r, \Y2r, \Y3r, \
		\Z0r, \Z1r, \Z2r, \Z3r, \
		\W0r, \W1r, \W2r, \W3r, \
		\TX,  \TY,  \TZ,  \TW, \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230
.endr

	a	\X0r, \X0r, \X0c
	a	\X1r, \X1r, \X1c
	a	\X2r, \X2r, \X2c
	a	\X3r, \X3r, \X3c
	a	\Y0r, \Y0r, \Y0c
	a	\Y1r, \Y1r, \Y1c
	a	\Y2r, \Y2r, \Y2c
	a	\Y3r, \Y3r, \Y3c
	a	\Z0r, \Z0r, \Z0c
	a	\Z1r, \Z1r, \Z1c
	a	\Z2r, \Z2r, \Z2c
	a	\Z3r, \Z3r, \Z3c
	a	\W0r, \W0r, \W0c
	a	\W1r, \W1r, \W1c
	a	\W2r, \W2r, \W2c
	a	\W3r, \W3r, \W3c
.endm

/*****************************************************************************/

.macro scrypt_spu_loop1 data, dma_vect_list, dma_vect_step, scratch_eahi \
                        tag1, tag_mask1, tag2, tag_mask2, \
                        idx, dma_vect_list_size, mfc_putl_cmd, dma_vect0, dma_vect1, dma_vect2, dma_vect3, \
                        dummy, mfc_tag_update_all, data_b, dma_vect_list_b, \
			aX0l, aX1l, aX2l, aX3l, \
			aY0l, aY1l, aY2l, aY3l, \
			aZ0l, aZ1l, aZ2l, aZ3l, \
			aW0l, aW1l, aW2l, aW3l, \
			aX0r, aX1r, aX2r, aX3r, \
			aY0r, aY1r, aY2r, aY3r, \
			aZ0r, aZ1r, aZ2r, aZ3r, \
			aW0r, aW1r, aW2r, aW3r, \
			bX0l, bX1l, bX2l, bX3l, \
			bY0l, bY1l, bY2l, bY3l, \
			bZ0l, bZ1l, bZ2l, bZ3l, \
			bW0l, bW1l, bW2l, bW3l, \
			bX0r, bX1r, bX2r, bX3r, \
			bY0r, bY1r, bY2r, bY3r, \
			bZ0r, bZ1r, bZ2r, bZ3r, \
			bW0r, bW1r, bW2r, bW3r, \
			X0c, X1c, X2c, X3c, \
			Y0c, Y1c, Y2c, Y3c, \
			Z0c, Z1c, Z2c, Z3c, \
			W0c, W1c, W2c, W3c, \
			TX,  TY,  TZ,  TW,  \
			X1t, X2t, X3t,      \
			Y1t, Y2t, Y3t,      \
			Z1t, Z2t, Z3t,      \
			W1t, W2t, W3t,      \
			MASK3012,           \
			MASK2301,           \
			MASK1230
	/* load shuffle masks */
					il	\idx, 1023
					il	\dma_vect_list_size, 32
					il	\mfc_putl_cmd, MFC_PUTL_CMD
					il	\mfc_tag_update_all, MFC_TAG_UPDATE_ALL
					ai	\data_b, \data, 2 * 8 * 16
					ai	\data_b, \data_b, 2 * 8 * 16
					ai	\dma_vect_list_b, \dma_vect_list, 32
					lqr	\MASK3012, shufmask3012
					lqr	\MASK2301, shufmask2301
					lqr	\MASK1230, shufmask1230

					lqd	\dma_vect0, 0 * 16(\dma_vect_list)
					lqd	\dma_vect1, 1 * 16(\dma_vect_list)
					lqd	\dma_vect2, 2 * 16(\dma_vect_list)
					lqd	\dma_vect3, 3 * 16(\dma_vect_list)

					lqd	\aX0l,	0 * 128 + 0 * 16(\data)
					lqd	\aX1l,	0 * 128 + 1 * 16(\data)
					lqd	\aX2l,	0 * 128 + 2 * 16(\data)
					lqd	\aX3l,	0 * 128 + 3 * 16(\data)
					lqd	\aX0r,	0 * 128 + 4 * 16(\data)
					lqd	\aX1r,	0 * 128 + 5 * 16(\data)
					lqd	\aX2r,	0 * 128 + 6 * 16(\data)
					lqd	\aX3r,	0 * 128 + 7 * 16(\data)

					lqd	\aY0l,	1 * 128 + 0 * 16(\data)
					lqd	\aY1l,	1 * 128 + 1 * 16(\data)
					lqd	\aY2l,	1 * 128 + 2 * 16(\data)
					lqd	\aY3l,	1 * 128 + 3 * 16(\data)
					lqd	\aY0r,	1 * 128 + 4 * 16(\data)
					lqd	\aY1r,	1 * 128 + 5 * 16(\data)
					lqd	\aY2r,	1 * 128 + 6 * 16(\data)
					lqd	\aY3r,	1 * 128 + 7 * 16(\data)

					lqd	\aZ0l,	2 * 128 + 0 * 16(\data)
					lqd	\aZ1l,	2 * 128 + 1 * 16(\data)
					lqd	\aZ2l,	2 * 128 + 2 * 16(\data)
					lqd	\aZ3l,	2 * 128 + 3 * 16(\data)
					lqd	\aZ0r,	2 * 128 + 4 * 16(\data)
					lqd	\aZ1r,	2 * 128 + 5 * 16(\data)
					lqd	\aZ2r,	2 * 128 + 6 * 16(\data)
					lqd	\aZ3r,	2 * 128 + 7 * 16(\data)

					lqd	\aW0l,	3 * 128 + 0 * 16(\data)
					lqd	\aW1l,	3 * 128 + 1 * 16(\data)
					lqd	\aW2l,	3 * 128 + 2 * 16(\data)
					lqd	\aW3l,	3 * 128 + 3 * 16(\data)
					lqd	\aW0r,	3 * 128 + 4 * 16(\data)
					lqd	\aW1r,	3 * 128 + 5 * 16(\data)
					lqd	\aW2r,	3 * 128 + 6 * 16(\data)
					lqd	\aW3r,	3 * 128 + 7 * 16(\data)

					lqd	\bX0l,	4 * 128 + 0 * 16(\data)
					lqd	\bX1l,	4 * 128 + 1 * 16(\data)
					lqd	\bX2l,	4 * 128 + 2 * 16(\data)
					lqd	\bX3l,	4 * 128 + 3 * 16(\data)
					lqd	\bX0r,	4 * 128 + 4 * 16(\data)
					lqd	\bX1r,	4 * 128 + 5 * 16(\data)
					lqd	\bX2r,	4 * 128 + 6 * 16(\data)
					lqd	\bX3r,	4 * 128 + 7 * 16(\data)

					lqd	\bY0l,	5 * 128 + 0 * 16(\data)
					lqd	\bY1l,	5 * 128 + 1 * 16(\data)
					lqd	\bY2l,	5 * 128 + 2 * 16(\data)
					lqd	\bY3l,	5 * 128 + 3 * 16(\data)
					lqd	\bY0r,	5 * 128 + 4 * 16(\data)
					lqd	\bY1r,	5 * 128 + 5 * 16(\data)
					lqd	\bY2r,	5 * 128 + 6 * 16(\data)
					lqd	\bY3r,	5 * 128 + 7 * 16(\data)

					lqd	\bZ0l,	6 * 128 + 0 * 16(\data)
					lqd	\bZ1l,	6 * 128 + 1 * 16(\data)
					lqd	\bZ2l,	6 * 128 + 2 * 16(\data)
					lqd	\bZ3l,	6 * 128 + 3 * 16(\data)
					lqd	\bZ0r,	6 * 128 + 4 * 16(\data)
					lqd	\bZ1r,	6 * 128 + 5 * 16(\data)
					lqd	\bZ2r,	6 * 128 + 6 * 16(\data)
					lqd	\bZ3r,	6 * 128 + 7 * 16(\data)

					lqd	\bW0l,	7 * 128 + 0 * 16(\data)
					lqd	\bW1l,	7 * 128 + 1 * 16(\data)
					lqd	\bW2l,	7 * 128 + 2 * 16(\data)
					lqd	\bW3l,	7 * 128 + 3 * 16(\data)
					lqd	\bW0r,	7 * 128 + 4 * 16(\data)
					lqd	\bW1r,	7 * 128 + 5 * 16(\data)
					lqd	\bW2r,	7 * 128 + 6 * 16(\data)
					lqd	\bW3r,	7 * 128 + 7 * 16(\data)

	dsync
	wrch	$ch16,	\data               // local storage address
	wrch	$ch17,	\scratch_eahi       // EAH
	wrch	$ch18,	\dma_vect_list      // list address
	wrch	$ch19,	\dma_vect_list_size // list size
	wrch	$ch20,	\tag1               // tag id
	wrch	$ch21,	\mfc_putl_cmd       // MFC_PUTL_CMD
0:
/*
	salsa20_8_xor4d	\aX0l, \aX1l, \aX2l, \aX3l, \
			\aY0l, \aY1l, \aY2l, \aY3l, \
			\aZ0l, \aZ1l, \aZ2l, \aZ3l, \
			\aW0l, \aW1l, \aW2l, \aW3l, \
			\aX0r, \aX1r, \aX2r, \aX3r, \
			\aY0r, \aY1r, \aY2r, \aY3r, \
			\aZ0r, \aZ1r, \aZ2r, \aZ3r, \
			\aW0r, \aW1r, \aW2r, \aW3r, \
			\X0c, \X1c, \X2c, \X3c, \
			\Y0c, \Y1c, \Y2c, \Y3c, \
			\Z0c, \Z1c, \Z2c, \Z3c, \
			\W0c, \W1c, \W2c, \W3c, \
			\TX,  \TY,  \TZ,  \TW,  \
			\X1t, \X2t, \X3t,      \
			\Y1t, \Y2t, \Y3t,      \
			\Z1t, \Z2t, \Z3t,      \
			\W1t, \W2t, \W3t,      \
			\MASK3012,             \
			\MASK2301,             \
			\MASK1230
*/
.balign 8
	a	\dma_vect2, \dma_vect2, \dma_vect_step
					wrch	$ch22,	\tag_mask2          // tag mask
	a	\dma_vect3, \dma_vect3, \dma_vect_step
					wrch	$ch23,	\mfc_tag_update_all // MFC_TAG_UPDATE_ALL
	xor	\X0c,	\aX0l,	\aX0r
	xor	\X1c,	\aX1l,	\aX1r
	xor	\X2c,	\aX2l,	\aX2r
	xor	\X3c,	\aX3l,	\aX3r
	xor	\Y0c,	\aY0l,	\aY0r
					rdch	\dummy,	$ch24               // read to dummy
	xor	\Y1c,	\aY1l,	\aY1r
					stqd	\dma_vect2, 2 * 16(\dma_vect_list)
	xor	\Y2c,	\aY2l,	\aY2r
					stqd	\dma_vect3, 3 * 16(\dma_vect_list)
	xor	\Y3c,	\aY3l,	\aY3r
					stqd	\bX0l,	4 * 128 + 0 * 16(\data)
	xor	\Z0c,	\aZ0l,	\aZ0r
					stqd	\bX1l,	4 * 128 + 1 * 16(\data)
	xor	\Z1c,	\aZ1l,	\aZ1r
					stqd	\bX2l,	4 * 128 + 2 * 16(\data)
	xor	\Z2c,	\aZ2l,	\aZ2r
					stqd	\bX3l,	4 * 128 + 3 * 16(\data)
	xor	\Z3c,	\aZ3l,	\aZ3r
					stqd	\bX0r,	4 * 128 + 4 * 16(\data)
	xor	\W0c,	\aW0l,	\aW0r
					stqd	\bX1r,	4 * 128 + 5 * 16(\data)
	xor	\W1c,	\aW1l,	\aW1r
					stqd	\bX2r,	4 * 128 + 6 * 16(\data)
	xor	\W2c,	\aW2l,	\aW2r
					stqd	\bX3r,	4 * 128 + 7 * 16(\data)
	xor	\W3c,	\aW3l,	\aW3r

.balign 8
	salsa20_8_step \
		\X0c, \X1c, \X2c, \X3c, \
		\Y0c, \Y1c, \Y2c, \Y3c, \
		\Z0c, \Z1c, \Z2c, \Z3c, \
		\W0c, \W1c, \W2c, \W3c, \
		\aX0l, \aX1l, \aX2l, \aX3l, \
		\aY0l, \aY1l, \aY2l, \aY3l, \
		\aZ0l, \aZ1l, \aZ2l, \aZ3l, \
		\aW0l, \aW1l, \aW2l, \aW3l, \
		\TX,  \TY,  \TZ,  \TW,  \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230

.balign 8
.rept 3
	salsa20_8_step \
		\aX0l, \aX1l, \aX2l, \aX3l, \
		\aY0l, \aY1l, \aY2l, \aY3l, \
		\aZ0l, \aZ1l, \aZ2l, \aZ3l, \
		\aW0l, \aW1l, \aW2l, \aW3l, \
		\aX0l, \aX1l, \aX2l, \aX3l, \
		\aY0l, \aY1l, \aY2l, \aY3l, \
		\aZ0l, \aZ1l, \aZ2l, \aZ3l, \
		\aW0l, \aW1l, \aW2l, \aW3l, \
		\TX,  \TY,  \TZ,  \TW, \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230
.endr

.balign 8
	a	\aX0l, \aX0l, \X0c
					stqd	\bY0l,	5 * 128 + 0 * 16(\data)
	a	\aX1l, \aX1l, \X1c
					stqd	\bY1l,	5 * 128 + 1 * 16(\data)
	a	\aX2l, \aX2l, \X2c
					stqd	\bY2l,	5 * 128 + 2 * 16(\data)
	a	\aX3l, \aX3l, \X3c
					stqd	\bY3l,	5 * 128 + 3 * 16(\data)
	a	\aY0l, \aY0l, \Y0c
					stqd	\bY0r,	5 * 128 + 4 * 16(\data)
	a	\aY1l, \aY1l, \Y1c
					stqd	\bY1r,	5 * 128 + 5 * 16(\data)
	a	\aY2l, \aY2l, \Y2c
					stqd	\bY2r,	5 * 128 + 6 * 16(\data)
	a	\aY3l, \aY3l, \Y3c
					stqd	\bY3r,	5 * 128 + 7 * 16(\data)
	a	\aZ0l, \aZ0l, \Z0c
	a	\aZ1l, \aZ1l, \Z1c
	a	\aZ2l, \aZ2l, \Z2c
	a	\aZ3l, \aZ3l, \Z3c
	a	\aW0l, \aW0l, \W0c
					stqd	\bZ0l,	6 * 128 + 0 * 16(\data)
	a	\aW1l, \aW1l, \W1c
					stqd	\bZ1l,	6 * 128 + 1 * 16(\data)
	a	\aW2l, \aW2l, \W2c
					stqd	\bZ2l,	6 * 128 + 2 * 16(\data)
	a	\aW3l, \aW3l, \W3c
					stqd	\bZ3l,	6 * 128 + 3 * 16(\data)
	xor	\X0c,	\aX0l,	\aX0r
					stqd	\bZ0r,	6 * 128 + 4 * 16(\data)
	xor	\X1c,	\aX1l,	\aX1r
					stqd	\bZ1r,	6 * 128 + 5 * 16(\data)
	xor	\X2c,	\aX2l,	\aX2r
					stqd	\bZ2r,	6 * 128 + 6 * 16(\data)
	xor	\X3c,	\aX3l,	\aX3r
					stqd	\bZ3r,	6 * 128 + 7 * 16(\data)
	xor	\Y0c,	\aY0l,	\aY0r
	xor	\Y1c,	\aY1l,	\aY1r
	xor	\Y2c,	\aY2l,	\aY2r
	xor	\Y3c,	\aY3l,	\aY3r
	xor	\Z0c,	\aZ0l,	\aZ0r
					stqd	\bW0l,	7 * 128 + 0 * 16(\data)
	xor	\Z1c,	\aZ1l,	\aZ1r
					stqd	\bW1l,	7 * 128 + 1 * 16(\data)
	xor	\Z2c,	\aZ2l,	\aZ2r
					stqd	\bW2l,	7 * 128 + 2 * 16(\data)
	xor	\Z3c,	\aZ3l,	\aZ3r
					stqd	\bW3l,	7 * 128 + 3 * 16(\data)
	xor	\W0c,	\aW0l,	\aW0r
					stqd	\bW0r,	7 * 128 + 4 * 16(\data)
	xor	\W1c,	\aW1l,	\aW1r
					stqd	\bW1r,	7 * 128 + 5 * 16(\data)
	xor	\W2c,	\aW2l,	\aW2r
					stqd	\bW2r,	7 * 128 + 6 * 16(\data)
	xor	\W3c,	\aW3l,	\aW3r
					stqd	\bW3r,	7 * 128 + 7 * 16(\data)

.balign 8
	salsa20_8_step \
		\X0c, \X1c, \X2c, \X3c, \
		\Y0c, \Y1c, \Y2c, \Y3c, \
		\Z0c, \Z1c, \Z2c, \Z3c, \
		\W0c, \W1c, \W2c, \W3c, \
		\aX0r, \aX1r, \aX2r, \aX3r, \
		\aY0r, \aY1r, \aY2r, \aY3r, \
		\aZ0r, \aZ1r, \aZ2r, \aZ3r, \
		\aW0r, \aW1r, \aW2r, \aW3r, \
		\TX,  \TY,  \TZ,  \TW,  \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230

.balign 8
.rept 3
	salsa20_8_step \
		\aX0r, \aX1r, \aX2r, \aX3r, \
		\aY0r, \aY1r, \aY2r, \aY3r, \
		\aZ0r, \aZ1r, \aZ2r, \aZ3r, \
		\aW0r, \aW1r, \aW2r, \aW3r, \
		\aX0r, \aX1r, \aX2r, \aX3r, \
		\aY0r, \aY1r, \aY2r, \aY3r, \
		\aZ0r, \aZ1r, \aZ2r, \aZ3r, \
		\aW0r, \aW1r, \aW2r, \aW3r, \
		\TX,  \TY,  \TZ,  \TW, \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230
.endr

.balign 8
	a	\aX0r, \aX0r, \X0c
					dsync
	a	\aX1r, \aX1r, \X1c
					wrch	$ch16,	\data_b             // local storage address
	a	\aX2r, \aX2r, \X2c
					wrch	$ch17,	\scratch_eahi       // EAH
	a	\aX3r, \aX3r, \X3c
					wrch	$ch18,	\dma_vect_list_b    // list address
	a	\aY0r, \aY0r, \Y0c
					wrch	$ch19,	\dma_vect_list_size // list size
	a	\aY1r, \aY1r, \Y1c
					wrch	$ch20,	\tag2               // tag id
	a	\aY2r, \aY2r, \Y2c
					wrch	$ch21,	\mfc_putl_cmd       // MFC_PUTL_CMD
	a	\aY3r, \aY3r, \Y3c
	a	\aZ0r, \aZ0r, \Z0c
	a	\aZ1r, \aZ1r, \Z1c
	a	\aZ2r, \aZ2r, \Z2c
	a	\aZ3r, \aZ3r, \Z3c
	a	\aW0r, \aW0r, \W0c
	a	\aW1r, \aW1r, \W1c
	a	\aW2r, \aW2r, \W2c
	a	\aW3r, \aW3r, \W3c
/*
	salsa20_8_xor4d	\bX0l, \bX1l, \bX2l, \bX3l, \
			\bY0l, \bY1l, \bY2l, \bY3l, \
			\bZ0l, \bZ1l, \bZ2l, \bZ3l, \
			\bW0l, \bW1l, \bW2l, \bW3l, \
			\bX0r, \bX1r, \bX2r, \bX3r, \
			\bY0r, \bY1r, \bY2r, \bY3r, \
			\bZ0r, \bZ1r, \bZ2r, \bZ3r, \
			\bW0r, \bW1r, \bW2r, \bW3r, \
			\X0c, \X1c, \X2c, \X3c, \
			\Y0c, \Y1c, \Y2c, \Y3c, \
			\Z0c, \Z1c, \Z2c, \Z3c, \
			\W0c, \W1c, \W2c, \W3c, \
			\TX,  \TY,  \TZ,  \TW,  \
			\X1t, \X2t, \X3t,      \
			\Y1t, \Y2t, \Y3t,      \
			\Z1t, \Z2t, \Z3t,      \
			\W1t, \W2t, \W3t,      \
			\MASK3012,             \
			\MASK2301,             \
			\MASK1230
*/
	a	\dma_vect0, \dma_vect0, \dma_vect_step
					wrch	$ch22,	\tag_mask1          // tag mask
	a	\dma_vect1, \dma_vect1, \dma_vect_step
					wrch	$ch23,	\mfc_tag_update_all // MFC_TAG_UPDATE_ALL
	xor	\X0c,	\bX0l,	\bX0r
	xor	\X1c,	\bX1l,	\bX1r
	xor	\X2c,	\bX2l,	\bX2r
	xor	\X3c,	\bX3l,	\bX3r
	xor	\Y0c,	\bY0l,	\bY0r
					rdch	\dummy,	$ch24               // read to dummy
	xor	\Y1c,	\bY1l,	\bY1r
					stqd	\dma_vect0, 0 * 16(\dma_vect_list)
	xor	\Y2c,	\bY2l,	\bY2r
					stqd	\dma_vect1, 1 * 16(\dma_vect_list)
	xor	\Y3c,	\bY3l,	\bY3r
					stqd	\aX0l,	0 * 128 + 0 * 16(\data)
	xor	\Z0c,	\bZ0l,	\bZ0r
					stqd	\aX1l,	0 * 128 + 1 * 16(\data)
	xor	\Z1c,	\bZ1l,	\bZ1r
					stqd	\aX2l,	0 * 128 + 2 * 16(\data)
	xor	\Z2c,	\bZ2l,	\bZ2r
					stqd	\aX3l,	0 * 128 + 3 * 16(\data)
	xor	\Z3c,	\bZ3l,	\bZ3r
					stqd	\aX0r,	0 * 128 + 4 * 16(\data)
	xor	\W0c,	\bW0l,	\bW0r
					stqd	\aX1r,	0 * 128 + 5 * 16(\data)
	xor	\W1c,	\bW1l,	\bW1r
					stqd	\aX2r,	0 * 128 + 6 * 16(\data)
	xor	\W2c,	\bW2l,	\bW2r
					stqd	\aX3r,	0 * 128 + 7 * 16(\data)
	xor	\W3c,	\bW3l,	\bW3r

.balign 8
	salsa20_8_step \
		\X0c, \X1c, \X2c, \X3c, \
		\Y0c, \Y1c, \Y2c, \Y3c, \
		\Z0c, \Z1c, \Z2c, \Z3c, \
		\W0c, \W1c, \W2c, \W3c, \
		\bX0l, \bX1l, \bX2l, \bX3l, \
		\bY0l, \bY1l, \bY2l, \bY3l, \
		\bZ0l, \bZ1l, \bZ2l, \bZ3l, \
		\bW0l, \bW1l, \bW2l, \bW3l, \
		\TX,  \TY,  \TZ,  \TW,  \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230

.balign 8
.rept 3
	salsa20_8_step \
		\bX0l, \bX1l, \bX2l, \bX3l, \
		\bY0l, \bY1l, \bY2l, \bY3l, \
		\bZ0l, \bZ1l, \bZ2l, \bZ3l, \
		\bW0l, \bW1l, \bW2l, \bW3l, \
		\bX0l, \bX1l, \bX2l, \bX3l, \
		\bY0l, \bY1l, \bY2l, \bY3l, \
		\bZ0l, \bZ1l, \bZ2l, \bZ3l, \
		\bW0l, \bW1l, \bW2l, \bW3l, \
		\TX,  \TY,  \TZ,  \TW, \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230
.endr

.balign 8
	a	\bX0l, \bX0l, \X0c
					stqd	\aY0l,	1 * 128 + 0 * 16(\data)
	a	\bX1l, \bX1l, \X1c
					stqd	\aY1l,	1 * 128 + 1 * 16(\data)
	a	\bX2l, \bX2l, \X2c
					stqd	\aY2l,	1 * 128 + 2 * 16(\data)
	a	\bX3l, \bX3l, \X3c
					stqd	\aY3l,	1 * 128 + 3 * 16(\data)
	a	\bY0l, \bY0l, \Y0c
					stqd	\aY0r,	1 * 128 + 4 * 16(\data)
	a	\bY1l, \bY1l, \Y1c
					stqd	\aY1r,	1 * 128 + 5 * 16(\data)
	a	\bY2l, \bY2l, \Y2c
					stqd	\aY2r,	1 * 128 + 6 * 16(\data)
	a	\bY3l, \bY3l, \Y3c
					stqd	\aY3r,	1 * 128 + 7 * 16(\data)
	a	\bZ0l, \bZ0l, \Z0c
	a	\bZ1l, \bZ1l, \Z1c
	a	\bZ2l, \bZ2l, \Z2c
	a	\bZ3l, \bZ3l, \Z3c
	a	\bW0l, \bW0l, \W0c
					stqd	\aZ0l,	2 * 128 + 0 * 16(\data)
	a	\bW1l, \bW1l, \W1c
					stqd	\aZ1l,	2 * 128 + 1 * 16(\data)
	a	\bW2l, \bW2l, \W2c
					stqd	\aZ2l,	2 * 128 + 2 * 16(\data)
	a	\bW3l, \bW3l, \W3c
					stqd	\aZ3l,	2 * 128 + 3 * 16(\data)
	xor	\X0c,	\bX0l,	\bX0r
					stqd	\aZ0r,	2 * 128 + 4 * 16(\data)
	xor	\X1c,	\bX1l,	\bX1r
					stqd	\aZ1r,	2 * 128 + 5 * 16(\data)
	xor	\X2c,	\bX2l,	\bX2r
					stqd	\aZ2r,	2 * 128 + 6 * 16(\data)
	xor	\X3c,	\bX3l,	\bX3r
					stqd	\aZ3r,	2 * 128 + 7 * 16(\data)
	xor	\Y0c,	\bY0l,	\bY0r
	xor	\Y1c,	\bY1l,	\bY1r
	xor	\Y2c,	\bY2l,	\bY2r
	xor	\Y3c,	\bY3l,	\bY3r
	xor	\Z0c,	\bZ0l,	\bZ0r
					stqd	\aW0l,	3 * 128 + 0 * 16(\data)
	xor	\Z1c,	\bZ1l,	\bZ1r
					stqd	\aW1l,	3 * 128 + 1 * 16(\data)
	xor	\Z2c,	\bZ2l,	\bZ2r
					stqd	\aW2l,	3 * 128 + 2 * 16(\data)
	xor	\Z3c,	\bZ3l,	\bZ3r
					stqd	\aW3l,	3 * 128 + 3 * 16(\data)
	xor	\W0c,	\bW0l,	\bW0r
					stqd	\aW0r,	3 * 128 + 4 * 16(\data)
	xor	\W1c,	\bW1l,	\bW1r
					stqd	\aW1r,	3 * 128 + 5 * 16(\data)
	xor	\W2c,	\bW2l,	\bW2r
					stqd	\aW2r,	3 * 128 + 6 * 16(\data)
	xor	\W3c,	\bW3l,	\bW3r
					stqd	\aW3r,	3 * 128 + 7 * 16(\data)

.balign 8
	salsa20_8_step \
		\X0c, \X1c, \X2c, \X3c, \
		\Y0c, \Y1c, \Y2c, \Y3c, \
		\Z0c, \Z1c, \Z2c, \Z3c, \
		\W0c, \W1c, \W2c, \W3c, \
		\bX0r, \bX1r, \bX2r, \bX3r, \
		\bY0r, \bY1r, \bY2r, \bY3r, \
		\bZ0r, \bZ1r, \bZ2r, \bZ3r, \
		\bW0r, \bW1r, \bW2r, \bW3r, \
		\TX,  \TY,  \TZ,  \TW,  \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230

.balign 8
.rept 3
	salsa20_8_step \
		\bX0r, \bX1r, \bX2r, \bX3r, \
		\bY0r, \bY1r, \bY2r, \bY3r, \
		\bZ0r, \bZ1r, \bZ2r, \bZ3r, \
		\bW0r, \bW1r, \bW2r, \bW3r, \
		\bX0r, \bX1r, \bX2r, \bX3r, \
		\bY0r, \bY1r, \bY2r, \bY3r, \
		\bZ0r, \bZ1r, \bZ2r, \bZ3r, \
		\bW0r, \bW1r, \bW2r, \bW3r, \
		\TX,  \TY,  \TZ,  \TW, \
		\X1t, \X2t, \X3t,      \
		\Y1t, \Y2t, \Y3t,      \
		\Z1t, \Z2t, \Z3t,      \
		\W1t, \W2t, \W3t,      \
		\MASK3012,             \
		\MASK2301,             \
		\MASK1230
.endr

.balign 8
	a	\bX0r, \bX0r, \X0c
					hbrr	1f, 0b
	a	\bX1r, \bX1r, \X1c
					dsync
	a	\bX2r, \bX2r, \X2c
					wrch	$ch16,	\data               // local storage address
	a	\bX3r, \bX3r, \X3c
					wrch	$ch17,	\scratch_eahi       // EAH
	a	\bY0r, \bY0r, \Y0c
					wrch	$ch18,	\dma_vect_list      // list address
	a	\bY1r, \bY1r, \Y1c
					wrch	$ch19,	\dma_vect_list_size // list size
	a	\bY2r, \bY2r, \Y2c
					wrch	$ch20,	\tag1               // tag id
	a	\bY3r, \bY3r, \Y3c
					wrch	$ch21,	\mfc_putl_cmd       // MFC_PUTL_CMD
	ai	\idx, \idx, -1
	a	\bZ0r, \bZ0r, \Z0c
	a	\bZ1r, \bZ1r, \Z1c
	a	\bZ2r, \bZ2r, \Z2c
	a	\bZ3r, \bZ3r, \Z3c
	a	\bW0r, \bW0r, \W0c
	a	\bW1r, \bW1r, \W1c
	a	\bW2r, \bW2r, \W2c
	a	\bW3r, \bW3r, \W3c
1:
	brnz	\idx, 0b

	/* end of loop */

	salsa20_8_xor4d	\aX0l, \aX1l, \aX2l, \aX3l, \
			\aY0l, \aY1l, \aY2l, \aY3l, \
			\aZ0l, \aZ1l, \aZ2l, \aZ3l, \
			\aW0l, \aW1l, \aW2l, \aW3l, \
			\aX0r, \aX1r, \aX2r, \aX3r, \
			\aY0r, \aY1r, \aY2r, \aY3r, \
			\aZ0r, \aZ1r, \aZ2r, \aZ3r, \
			\aW0r, \aW1r, \aW2r, \aW3r, \
			\X0c, \X1c, \X2c, \X3c, \
			\Y0c, \Y1c, \Y2c, \Y3c, \
			\Z0c, \Z1c, \Z2c, \Z3c, \
			\W0c, \W1c, \W2c, \W3c, \
			\TX,  \TY,  \TZ,  \TW,  \
			\X1t, \X2t, \X3t,      \
			\Y1t, \Y2t, \Y3t,      \
			\Z1t, \Z2t, \Z3t,      \
			\W1t, \W2t, \W3t,      \
			\MASK3012,             \
			\MASK2301,             \
			\MASK1230

	wrch	$ch22,	\tag_mask2          // tag mask
	wrch	$ch23,	\mfc_tag_update_all // MFC_TAG_UPDATE_ALL
	rdch	\dummy,	$ch24               // read to dummy

	a	\dma_vect2, \dma_vect2, \dma_vect_step
	a	\dma_vect3, \dma_vect3, \dma_vect_step

	stqd	\dma_vect2, 2 * 16(\dma_vect_list)
	stqd	\dma_vect3, 3 * 16(\dma_vect_list)

	stqd	\bX0l,	4 * 128 + 0 * 16(\data)
	stqd	\bX1l,	4 * 128 + 1 * 16(\data)
	stqd	\bX2l,	4 * 128 + 2 * 16(\data)
	stqd	\bX3l,	4 * 128 + 3 * 16(\data)
	stqd	\bX0r,	4 * 128 + 4 * 16(\data)
	stqd	\bX1r,	4 * 128 + 5 * 16(\data)
	stqd	\bX2r,	4 * 128 + 6 * 16(\data)
	stqd	\bX3r,	4 * 128 + 7 * 16(\data)

	stqd	\bY0l,	5 * 128 + 0 * 16(\data)
	stqd	\bY1l,	5 * 128 + 1 * 16(\data)
	stqd	\bY2l,	5 * 128 + 2 * 16(\data)
	stqd	\bY3l,	5 * 128 + 3 * 16(\data)
	stqd	\bY0r,	5 * 128 + 4 * 16(\data)
	stqd	\bY1r,	5 * 128 + 5 * 16(\data)
	stqd	\bY2r,	5 * 128 + 6 * 16(\data)
	stqd	\bY3r,	5 * 128 + 7 * 16(\data)

	stqd	\bZ0l,	6 * 128 + 0 * 16(\data)
	stqd	\bZ1l,	6 * 128 + 1 * 16(\data)
	stqd	\bZ2l,	6 * 128 + 2 * 16(\data)
	stqd	\bZ3l,	6 * 128 + 3 * 16(\data)
	stqd	\bZ0r,	6 * 128 + 4 * 16(\data)
	stqd	\bZ1r,	6 * 128 + 5 * 16(\data)
	stqd	\bZ2r,	6 * 128 + 6 * 16(\data)
	stqd	\bZ3r,	6 * 128 + 7 * 16(\data)

	stqd	\bW0l,	7 * 128 + 0 * 16(\data)
	stqd	\bW1l,	7 * 128 + 1 * 16(\data)
	stqd	\bW2l,	7 * 128 + 2 * 16(\data)
	stqd	\bW3l,	7 * 128 + 3 * 16(\data)
	stqd	\bW0r,	7 * 128 + 4 * 16(\data)
	stqd	\bW1r,	7 * 128 + 5 * 16(\data)
	stqd	\bW2r,	7 * 128 + 6 * 16(\data)
	stqd	\bW3r,	7 * 128 + 7 * 16(\data)

	dsync
	wrch	$ch16,	\data_b             // local storage address
	wrch	$ch17,	\scratch_eahi       // EAH
	wrch	$ch18,	\dma_vect_list_b    // list address
	wrch	$ch19,	\dma_vect_list_size // list size
	wrch	$ch20,	\tag2               // tag id
	wrch	$ch21,	\mfc_putl_cmd       // MFC_PUTL_CMD

	salsa20_8_xor4d	\bX0l, \bX1l, \bX2l, \bX3l, \
			\bY0l, \bY1l, \bY2l, \bY3l, \
			\bZ0l, \bZ1l, \bZ2l, \bZ3l, \
			\bW0l, \bW1l, \bW2l, \bW3l, \
			\bX0r, \bX1r, \bX2r, \bX3r, \
			\bY0r, \bY1r, \bY2r, \bY3r, \
			\bZ0r, \bZ1r, \bZ2r, \bZ3r, \
			\bW0r, \bW1r, \bW2r, \bW3r, \
			\X0c, \X1c, \X2c, \X3c, \
			\Y0c, \Y1c, \Y2c, \Y3c, \
			\Z0c, \Z1c, \Z2c, \Z3c, \
			\W0c, \W1c, \W2c, \W3c, \
			\TX,  \TY,  \TZ,  \TW,  \
			\X1t, \X2t, \X3t,      \
			\Y1t, \Y2t, \Y3t,      \
			\Z1t, \Z2t, \Z3t,      \
			\W1t, \W2t, \W3t,      \
			\MASK3012,             \
			\MASK2301,             \
			\MASK1230

	wrch	$ch22,	\tag_mask1          // tag mask
	wrch	$ch23,	\mfc_tag_update_all // MFC_TAG_UPDATE_ALL
	rdch	\dummy,	$ch24               // read to dummy
	wrch	$ch22,	\tag_mask2          // tag mask
	wrch	$ch23,	\mfc_tag_update_all // MFC_TAG_UPDATE_ALL
	rdch	\dummy,	$ch24               // read to dummy

	stqd	\aX0l,	0 * 128 + 0 * 16(\data)
	stqd	\aX1l,	0 * 128 + 1 * 16(\data)
	stqd	\aX2l,	0 * 128 + 2 * 16(\data)
	stqd	\aX3l,	0 * 128 + 3 * 16(\data)
	stqd	\aX0r,	0 * 128 + 4 * 16(\data)
	stqd	\aX1r,	0 * 128 + 5 * 16(\data)
	stqd	\aX2r,	0 * 128 + 6 * 16(\data)
	stqd	\aX3r,	0 * 128 + 7 * 16(\data)

	stqd	\aY0l,	1 * 128 + 0 * 16(\data)
	stqd	\aY1l,	1 * 128 + 1 * 16(\data)
	stqd	\aY2l,	1 * 128 + 2 * 16(\data)
	stqd	\aY3l,	1 * 128 + 3 * 16(\data)
	stqd	\aY0r,	1 * 128 + 4 * 16(\data)
	stqd	\aY1r,	1 * 128 + 5 * 16(\data)
	stqd	\aY2r,	1 * 128 + 6 * 16(\data)
	stqd	\aY3r,	1 * 128 + 7 * 16(\data)

	stqd	\aZ0l,	2 * 128 + 0 * 16(\data)
	stqd	\aZ1l,	2 * 128 + 1 * 16(\data)
	stqd	\aZ2l,	2 * 128 + 2 * 16(\data)
	stqd	\aZ3l,	2 * 128 + 3 * 16(\data)
	stqd	\aZ0r,	2 * 128 + 4 * 16(\data)
	stqd	\aZ1r,	2 * 128 + 5 * 16(\data)
	stqd	\aZ2r,	2 * 128 + 6 * 16(\data)
	stqd	\aZ3r,	2 * 128 + 7 * 16(\data)

	stqd	\aW0l,	3 * 128 + 0 * 16(\data)
	stqd	\aW1l,	3 * 128 + 1 * 16(\data)
	stqd	\aW2l,	3 * 128 + 2 * 16(\data)
	stqd	\aW3l,	3 * 128 + 3 * 16(\data)
	stqd	\aW0r,	3 * 128 + 4 * 16(\data)
	stqd	\aW1r,	3 * 128 + 5 * 16(\data)
	stqd	\aW2r,	3 * 128 + 6 * 16(\data)
	stqd	\aW3r,	3 * 128 + 7 * 16(\data)

	stqd	\bX0l,	4 * 128 + 0 * 16(\data)
	stqd	\bX1l,	4 * 128 + 1 * 16(\data)
	stqd	\bX2l,	4 * 128 + 2 * 16(\data)
	stqd	\bX3l,	4 * 128 + 3 * 16(\data)
	stqd	\bX0r,	4 * 128 + 4 * 16(\data)
	stqd	\bX1r,	4 * 128 + 5 * 16(\data)
	stqd	\bX2r,	4 * 128 + 6 * 16(\data)
	stqd	\bX3r,	4 * 128 + 7 * 16(\data)

	stqd	\bY0l,	5 * 128 + 0 * 16(\data)
	stqd	\bY1l,	5 * 128 + 1 * 16(\data)
	stqd	\bY2l,	5 * 128 + 2 * 16(\data)
	stqd	\bY3l,	5 * 128 + 3 * 16(\data)
	stqd	\bY0r,	5 * 128 + 4 * 16(\data)
	stqd	\bY1r,	5 * 128 + 5 * 16(\data)
	stqd	\bY2r,	5 * 128 + 6 * 16(\data)
	stqd	\bY3r,	5 * 128 + 7 * 16(\data)

	stqd	\bZ0l,	6 * 128 + 0 * 16(\data)
	stqd	\bZ1l,	6 * 128 + 1 * 16(\data)
	stqd	\bZ2l,	6 * 128 + 2 * 16(\data)
	stqd	\bZ3l,	6 * 128 + 3 * 16(\data)
	stqd	\bZ0r,	6 * 128 + 4 * 16(\data)
	stqd	\bZ1r,	6 * 128 + 5 * 16(\data)
	stqd	\bZ2r,	6 * 128 + 6 * 16(\data)
	stqd	\bZ3r,	6 * 128 + 7 * 16(\data)

	stqd	\bW0l,	7 * 128 + 0 * 16(\data)
	stqd	\bW1l,	7 * 128 + 1 * 16(\data)
	stqd	\bW2l,	7 * 128 + 2 * 16(\data)
	stqd	\bW3l,	7 * 128 + 3 * 16(\data)
	stqd	\bW0r,	7 * 128 + 4 * 16(\data)
	stqd	\bW1r,	7 * 128 + 5 * 16(\data)
	stqd	\bW2r,	7 * 128 + 6 * 16(\data)
	stqd	\bW3r,	7 * 128 + 7 * 16(\data)
.endm

	.align	3
	.type	scrypt_spu_loop1_asm, @function
scrypt_spu_loop1_asm:
	save_regs        80, 120
	scrypt_spu_loop1 $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14, \
			 $15, $16, $17, $18, $19, $20, $21, $22, $23, $24, $25, \
			 $26, $27, $28, $29, $30, $31, $32, $33, $34, $35, $36, \
			 $37, $38, $39, $40, $41, $42, $43, $44, $45, $46, $47, \
			 $48, $49, $50, $51, $52, $53, $54, $55, $56, $57, $58, \
			 $59, $60, $61, $62, $63, $64, $65, $66, $67, $68, $69, \
			 $70, $71, $72, $73, $74, $75, $76, $77, $78, $79, $80, \
			 $81, $82, $83, $84, $85, $86, $87, $88, $89, $90, $91, \
			 $92, $93, $94, $95, $96, $97, $98, $99, $100, $101, \
			 $102, $103, $104, $105, $106, $107, $108, $109, $110, \
			 $111, $112, $113, $114, $115, $116, $117, $118, $119, $120
	restore_regs     80, 120
	bi	$lr
