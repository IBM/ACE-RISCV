# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# Restores the remaining hypervisor's hart state and eventually resumes the hypervisor execution.
# We do not store the security monitor's state because the security monitor's execution is stateless. 
# 
# # Safety
#
# The caller must ensure that:
#   * `a0` stores the address of the dump hart area of the currently executing hardware hart.
# The function guarantees that on return:
#   * `mscratch` contains the address of the dump hart area of the currently executing hardware hart.
.globl exit_to_hypervisor_asm
.align 4
exit_to_hypervisor_asm:
    csrr        t6, mscratch

    ld          t0, ({HART_MEPC_OFFSET})(t6)
    csrw        mepc, t0
    ld          t0, ({HART_MSTATUS_OFFSET})(t6)
    csrw        mstatus, t0

    # restore from memory the hypervisor's processor state
    ld	        ra, ({HART_RA_OFFSET})(t6)
    ld	        sp, ({HART_SP_OFFSET})(t6)
    ld	        gp, ({HART_GP_OFFSET})(t6)
    ld	        tp, ({HART_TP_OFFSET})(t6)
    ld	        t0, ({HART_T0_OFFSET})(t6)
    ld	        t1, ({HART_T1_OFFSET})(t6)
    ld	        t2, ({HART_T2_OFFSET})(t6)
    ld	        s0, ({HART_S0_OFFSET})(t6)
    ld	        s1, ({HART_S1_OFFSET})(t6)
    ld	        a0, ({HART_A0_OFFSET})(t6)
    ld	        a1, ({HART_A1_OFFSET})(t6)
    ld	        a2, ({HART_A2_OFFSET})(t6)
    ld	        a3, ({HART_A3_OFFSET})(t6)
    ld	        a4, ({HART_A4_OFFSET})(t6)
    ld	        a5, ({HART_A5_OFFSET})(t6)
    ld	        a6, ({HART_A6_OFFSET})(t6)
    ld	        a7, ({HART_A7_OFFSET})(t6)
    ld	        s2, ({HART_S2_OFFSET})(t6)
    ld	        s3, ({HART_S3_OFFSET})(t6)
    ld	        s4, ({HART_S4_OFFSET})(t6)
    ld	        s5, ({HART_S5_OFFSET})(t6)
    ld	        s6, ({HART_S6_OFFSET})(t6)
    ld	        s7, ({HART_S7_OFFSET})(t6)
    ld	        s8, ({HART_S8_OFFSET})(t6)
    ld	        s9, ({HART_S9_OFFSET})(t6)
    ld	        s10, ({HART_S10_OFFSET})(t6)
    ld	        s11, ({HART_S11_OFFSET})(t6)
    ld	        t3, ({HART_T3_OFFSET})(t6)
    ld	        t4, ({HART_T4_OFFSET})(t6)
    ld	        t5, ({HART_T5_OFFSET})(t6)
    ld	        t6, ({HART_T6_OFFSET})(t6)
    mret    
