# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# Traps on exceptions or interrupts occurring during the confidential hart's execution. This is an entry point to the security monitor.
#
# # Safety
#
# The caller must ensure that:
#   * `mscratch` contains the address of the dump hart area of the currently executing hardware hart. 
#   * `sscratch` contains the address of the dump hart area of the confidential hart scheduled on this hardware hart.
.globl enter_from_confidential_hart_asm
# The trap vector address must be aligned to 4 bytes according to the RISC-V spec (see `stvec`).
.align 4
enter_from_confidential_hart_asm:
    csrrw	      a0,	sscratch, a0
    # Store current processor state (except for `a0`) in the dump hart area of the confidential hart.
    sd	        ra, ({HART_RA_OFFSET})(a0)
    sd	        sp, ({HART_SP_OFFSET})(a0)
    sd	        gp, ({HART_GP_OFFSET})(a0)
    sd	        tp, ({HART_TP_OFFSET})(a0)
    sd	        t0, ({HART_T0_OFFSET})(a0)
    sd	        t1, ({HART_T1_OFFSET})(a0)
    sd	        t2, ({HART_T2_OFFSET})(a0)
    sd	        s0, ({HART_S0_OFFSET})(a0)
    sd	        s1, ({HART_S1_OFFSET})(a0)
  # sd	        a0, ({HART_A0_OFFSET})(a0)
    sd	        a1, ({HART_A1_OFFSET})(a0)
    sd	        a2, ({HART_A2_OFFSET})(a0)
    sd	        a3, ({HART_A3_OFFSET})(a0)
    sd	        a4, ({HART_A4_OFFSET})(a0)
    sd	        a5, ({HART_A5_OFFSET})(a0)
    sd	        a6, ({HART_A6_OFFSET})(a0)
    sd	        a7, ({HART_A7_OFFSET})(a0)
    sd	        s2, ({HART_S2_OFFSET})(a0)
    sd	        s3, ({HART_S3_OFFSET})(a0)
    sd	        s4, ({HART_S4_OFFSET})(a0)
    sd	        s5, ({HART_S5_OFFSET})(a0)
    sd	        s6, ({HART_S6_OFFSET})(a0)
    sd	        s7, ({HART_S7_OFFSET})(a0)
    sd	        s8, ({HART_S8_OFFSET})(a0)
    sd	        s9, ({HART_S9_OFFSET})(a0)
    sd	        s10, ({HART_S10_OFFSET})(a0)
    sd	        s11, ({HART_S11_OFFSET})(a0)
    sd	        t3, ({HART_T3_OFFSET})(a0)
    sd	        t4, ({HART_T4_OFFSET})(a0)
    sd	        t5, ({HART_T5_OFFSET})(a0)
    sd	        t6, ({HART_T6_OFFSET})(a0)

    csrr        t0, mepc
    sd	        t0, ({HART_MEPC_OFFSET})(a0)
    csrr        t0, mstatus
    sd	        t0, ({HART_MSTATUS_OFFSET})(a0) 

    # Store the original `a0`
    csrrw	      t0,	sscratch, a0
    sd	        t0, ({HART_A0_OFFSET})(a0)

    # Recover the stack pointer for this hart. 
    # The stack pointer is stored in the memory dump area of the hart (pointed by `mscratch`)
    csrr        a0, mscratch
    ld	        sp, ({HART_STACK_ADDRESS_OFFSET})(a0)

    # Before calling Rust code, we must guarantee that: 
    #   * `mscratch` points to the dump area of this hardware hart
    #   * `sscratch` points to the dump area of the confidential hart assigned to this hardware hart
    #   * `a0` is the pointer to the dump area of this hardware hart
    j           route_trap_from_confidential_hart
