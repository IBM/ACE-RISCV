# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# Restores the remaining hypervisor's hart state and eventually resumes the hypervisor execution.
# We do not store the security monitor's state because the security monitor's execution is stateless. 
# 
# Safety
#
# The caller must ensure that `a0` stores the address of the dump hart area of the currently executing hardware hart.
.globl exit_to_hypervisor_asm
.align 4
exit_to_hypervisor_asm:
    csrr        a0, mscratch

    # restore from memory the hypervisor's processor state
    ld	        ra, ({HART_RA_OFFSET})(a0)
    ld	        sp, ({HART_SP_OFFSET})(a0)
    ld	        gp, ({HART_GP_OFFSET})(a0)
    ld	        tp, ({HART_TP_OFFSET})(a0)
  # ld	        t0, ({HART_T0_OFFSET})(a0)
    ld	        t1, ({HART_T1_OFFSET})(a0)
    ld	        t2, ({HART_T2_OFFSET})(a0)
    ld	        s0, ({HART_S0_OFFSET})(a0)
    ld	        s1, ({HART_S1_OFFSET})(a0)
  # ld	        a0, ({HART_A0_OFFSET})(a0)
    ld	        a1, ({HART_A1_OFFSET})(a0)
    ld	        a2, ({HART_A2_OFFSET})(a0)
    ld	        a3, ({HART_A3_OFFSET})(a0)
    ld	        a4, ({HART_A4_OFFSET})(a0)
    ld	        a5, ({HART_A5_OFFSET})(a0)
    ld	        a6, ({HART_A6_OFFSET})(a0)
    ld	        a7, ({HART_A7_OFFSET})(a0)
    ld	        s2, ({HART_S2_OFFSET})(a0)
    ld	        s3, ({HART_S3_OFFSET})(a0)
    ld	        s4, ({HART_S4_OFFSET})(a0)
    ld	        s5, ({HART_S5_OFFSET})(a0)
    ld	        s6, ({HART_S6_OFFSET})(a0)
    ld	        s7, ({HART_S7_OFFSET})(a0)
    ld	        s8, ({HART_S8_OFFSET})(a0)
    ld	        s9, ({HART_S9_OFFSET})(a0)
    ld	        s10, ({HART_S10_OFFSET})(a0)
    ld	        s11, ({HART_S11_OFFSET})(a0)
    ld	        t3, ({HART_T3_OFFSET})(a0)
    ld	        t4, ({HART_T4_OFFSET})(a0)
    ld	        t5, ({HART_T5_OFFSET})(a0)
    ld	        t6, ({HART_T6_OFFSET})(a0)

    # After mret the processor will set the hart's program counter to the `mepc` value.
    ld          t0, ({HART_MEPC_OFFSET})(a0)
    csrw        mepc, t0
    ld          t0, ({HART_MSTATUS_OFFSET})(a0)
    csrw        mstatus, t0
    # We do not have to set the `mtvec` because it was set during the initialization and it is then always set during context 
    # switches of security domains.

    # Restore from memory the `t0` and `a0` registers
    ld	        t0, ({HART_T0_OFFSET})(a0)
    ld	        a0, ({HART_A0_OFFSET})(a0)

    # Hey developer, check if you satisfy the safety conditions before going back to the hypervisor!
    mret    
