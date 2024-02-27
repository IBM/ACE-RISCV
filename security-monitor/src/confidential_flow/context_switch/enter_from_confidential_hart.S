# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# Traps on exceptions or interrupts occurring during the confidential hart's execution. This is an entry point to the security monitor.
#
# Safety: 
#
# The caller must ensure that:
#   * `mscratch` stores the address of the dump hart area of the currently executing hardware hart. 
#   * `sscratch` stores the address of the dump hart area of the confidential hart scheduled on this hardware hart.
.globl enter_from_confidential_hart_asm
# The trap vector address must be aligned to 4 bytes according to the RISC-V spec (see `stvec`).
.align 4
enter_from_confidential_hart_asm:
    # Temporary store a0 in sscratch, and set the address of the memory dump area in the a0 register.
    csrrw	    a0,	sscratch, a0

    # Store current processor state (except for a0) in the dump hart area of the confidential hart.
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

    # Check if the fp extension is available before restoring. Bits 13 and 14 of the sstatus encode this information.
    sd          t0, ({HART_SSTATUS_OFFSET})(a0)
    sra         t0, t0, 13
    add         t0, t0, 0b11
    beqz	    t0, 1f
    # Store the float pointing registers
    fsd	        f0, ({HART_F0_OFFSET})(a0)
    fsd	        f1, ({HART_F1_OFFSET})(a0)
    fsd	        f2, ({HART_F2_OFFSET})(a0)
    fsd	        f3, ({HART_F3_OFFSET})(a0)
    fsd	        f4, ({HART_F4_OFFSET})(a0)
    fsd	        f5, ({HART_F5_OFFSET})(a0)
    fsd	        f6, ({HART_F6_OFFSET})(a0)
    fsd	        f7, ({HART_F7_OFFSET})(a0)
    fsd	        f8, ({HART_F8_OFFSET})(a0)
    fsd	        f9, ({HART_F9_OFFSET})(a0)
    fsd	        f10, ({HART_F10_OFFSET})(a0)
    fsd	        f11, ({HART_F11_OFFSET})(a0)
    fsd	        f12, ({HART_F12_OFFSET})(a0)
    fsd	        f13, ({HART_F13_OFFSET})(a0)
    fsd	        f14, ({HART_F14_OFFSET})(a0)
    fsd	        f15, ({HART_F15_OFFSET})(a0)
    fsd	        f16, ({HART_F16_OFFSET})(a0)
    fsd	        f17, ({HART_F17_OFFSET})(a0)
    fsd	        f18, ({HART_F18_OFFSET})(a0)
    fsd	        f19, ({HART_F19_OFFSET})(a0)
    fsd	        f20, ({HART_F20_OFFSET})(a0)
    fsd	        f21, ({HART_F21_OFFSET})(a0)
    fsd	        f22, ({HART_F22_OFFSET})(a0)
    fsd	        f23, ({HART_F23_OFFSET})(a0)
    fsd	        f24, ({HART_F24_OFFSET})(a0)
    fsd	        f25, ({HART_F25_OFFSET})(a0)
    fsd	        f26, ({HART_F26_OFFSET})(a0)
    fsd	        f27, ({HART_F27_OFFSET})(a0)
    fsd	        f28, ({HART_F28_OFFSET})(a0)
    fsd	        f29, ({HART_F29_OFFSET})(a0)
    fsd	        f30, ({HART_F30_OFFSET})(a0)
    fsd	        f31, ({HART_F31_OFFSET})(a0)
    frcsr       t0
    sd          t0, ({HART_FCSR_OFFSET})(a0)

1:
    # store control status registers
    csrr        t0, mepc
    sd	        t0, ({HART_MEPC_OFFSET})(a0)
    csrr        t0, mstatus
    sd	        t0, ({HART_MSTATUS_OFFSET})(a0) 

    # Store the original `a0`
    csrr        t0, sscratch
    sd	        t0, ({HART_A0_OFFSET})(a0)

    # Recover the stack pointer for this hart by storing in the mscratch the address of the memory dump area of the hart
    csrr        a0, mscratch
    ld	        sp, ({HART_STACK_ADDRESS_OFFSET})(a0)

    # Make sure that: 
    #   * `mscratch` points to the dump area of this hardware hart
    #   * `sscratch` points to the dump area of the confidential hart assigned to this hardware hart
    j        enter_from_confidential_hart
