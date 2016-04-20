# *****************************************************************
#
#               The Compcert verified compiler
#
#           Xavier Leroy, INRIA Paris-Rocquencourt
#
# Copyright (c) 2013 Institut National de Recherche en Informatique et
#  en Automatique.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of the <organization> nor the
#       names of its contributors may be used to endorse or promote products
#       derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
# HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
# PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
# PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# *********************************************************************

# Adapted for RV32G by Prashanth Mundkur, SRI International.

# Helper functions for variadic functions <stdarg.h>.  RV32 version.

# typedef void * va_list;
# unsigned int __compcert_va_int32(va_list * ap);
# unsigned long long __compcert_va_int64(va_list * ap);
# double __compcert_va_float64(va_list * ap);

	.text

	.balign 16
	.globl __compcert_va_int32
__compcert_va_int32:
				# a0 = ap parameter
	lw	t5, 0(a0)	# t5 = pointer to next argument
	addi	t5, t5, 4	# advance ap by 4
	sw	t5, 0(a0)	# update ap
	addi	t5, t5, -4	# rewind to incoming next argument
	lw	a0, 0(t5)	# load it and return it in a0
	jr	ra
	.type	__compcert_va_int32, @function
	.size	__compcert_va_int32, .-__compcert_va_int32

	.balign 16
	.globl __compcert_va_int64
__compcert_va_int64:
				# a0 = ap parameter
	lw	t5, 0(a0)	# t5 = pointer to next argument
	addi	t5, t5, 15	# 8-align and advance by 8
	and	t5, t5, -8
	sw	t5, 0(a0)	# update ap
	addi	t5, t5, -8	# rewind to incoming next argument
	lw	a0, 0(t5)	# return it in [a0,a1]
	lw	a1, 4(t5)
	jr	ra
	.type	__compcert_va_int64, @function
	.size	__compcert_va_int64, .-__compcert_va_int64

	.balign 16
	.globl __compcert_va_float64
__compcert_va_float64:
	.type	__compcert_va_float64, @function
	.size	__compcert_va_float64, .-__compcert_va_float64
				# a0 = ap parameter
	lw	t5, 0(a0)	# t5 = pointer to next argument
	addi	t5, t5, 15	# 8-align and advance by 8
	and	t5, t5, -8
	sw	t5, 0(a0)	# update ap
	addi	t5, t5, -8	# rewind to incoming next argument
	fld	fa0, 0(t5)	# return it in fa0
	jr	ra
	.type	__compcert_va_float64, @function
	.size	__compcert_va_float64, .-__compcert_va_float64

# this is a placeholder since the spec is not clear
	.balign 16
	.globl __compcert_va_composite
__compcert_va_composite:
				# a0 = ap parameter
				# a1 = size of the composite, in bytes
	lw	t5, 0(a0)	# t5 = pointer to next argument
	add	t6, t5, a1	# advance by size
	add	t6, t6, 3	# 4-align
	and	t6, t6, -4
	sw	t6, 0(a0)	# update ap
	mv	a0, t5		# result is pointer to composite in stack
	jr	ra
	.type   __compcert_va_composite, @function
	.size   __compcert_va_composite, .-__compcert_va_composite
