# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# common definitions used by all assembly files goes here. Also this file should be included as a first one by the asm.rs
.set MSTATUS_MPV_SHIFT, 39
.set MSTATUS_MPP_SHIFT, 11
# machine previous interrupt enable (MPIE)
.set MSTATUS_MPIE_SHIFT, 7
.set MSTATUS_SUPERVISOR, 0b01


# Restores the remaining confidential's hart state and eventually resumes the confidential VM execution.
# We do not store the security monitor's state because the security monitor's execution is stateless. 
# 
# Safety
#
# The caller must ensure that:
#   * `mscratch` stores the address of the dump hart area of the currently executing hardware hart. 
#   * `sscratch` stores the address of the dump hart area of the confidential hart scheduled on this hardware hart.
.globl exit_to_confidential_hart_asm
# The trap vector address must be aligned to 4 bytes according to the RISC-V spec (see `stvec`).
.align 4
exit_to_confidential_hart_asm:
    # Should we maintain the mstatus when entering the confidential VM?
	li		    t0, (0b01 << MSTATUS_MPP_SHIFT) | (0b1 << MSTATUS_MPV_SHIFT) | (1 << MSTATUS_MPIE_SHIFT) | (1 << 5)
    ld          t1, ({HART_MSTATUS_OFFSET})(a0)
    or          t0, t0, t1
	csrw	    mstatus, t0

    ld          t0, ({HART_MEPC_OFFSET})(a0)
    csrw        mepc, t0
    la		    t0, enter_from_confidential_hart_asm
	csrw	    mtvec, t0

    # check if the fp extension is available before restoring.
    # Bits 13 and 14 of the sstatus encode this information.
    sd          t0, ({HART_SSTATUS_OFFSET})(a0)
    sra         t0, t0, 13
    add         t0, t0, 0b11
    beqz	    t0, 1f
    # restore fp registers
    sd          t0, ({HART_FCSR_OFFSET})(a0)
    fscsr       t0
    fld	        f0, ({HART_F0_OFFSET})(a0)
    fld	        f1, ({HART_F1_OFFSET})(a0)
    fld	        f2, ({HART_F2_OFFSET})(a0)
    fld	        f3, ({HART_F3_OFFSET})(a0)
    fld	        f4, ({HART_F4_OFFSET})(a0)
    fld	        f5, ({HART_F5_OFFSET})(a0)
    fld	        f6, ({HART_F6_OFFSET})(a0)
    fld	        f7, ({HART_F7_OFFSET})(a0)
    fld	        f8, ({HART_F8_OFFSET})(a0)
    fld	        f9, ({HART_F9_OFFSET})(a0)
    fld	        f10, ({HART_F10_OFFSET})(a0)
    fld	        f11, ({HART_F11_OFFSET})(a0)
    fld	        f12, ({HART_F12_OFFSET})(a0)
    fld	        f13, ({HART_F13_OFFSET})(a0)
    fld	        f14, ({HART_F14_OFFSET})(a0)
    fld	        f15, ({HART_F15_OFFSET})(a0)
    fld	        f16, ({HART_F16_OFFSET})(a0)
    fld	        f17, ({HART_F17_OFFSET})(a0)
    fld	        f18, ({HART_F18_OFFSET})(a0)
    fld	        f19, ({HART_F19_OFFSET})(a0)
    fld	        f20, ({HART_F20_OFFSET})(a0)
    fld	        f21, ({HART_F21_OFFSET})(a0)
    fld	        f22, ({HART_F22_OFFSET})(a0)
    fld	        f23, ({HART_F23_OFFSET})(a0)
    fld	        f24, ({HART_F24_OFFSET})(a0)
    fld	        f25, ({HART_F25_OFFSET})(a0)
    fld	        f26, ({HART_F26_OFFSET})(a0)
    fld	        f27, ({HART_F27_OFFSET})(a0)
    fld	        f28, ({HART_F28_OFFSET})(a0)
    fld	        f29, ({HART_F29_OFFSET})(a0)
    fld	        f30, ({HART_F30_OFFSET})(a0)
    fld	        f31, ({HART_F31_OFFSET})(a0)
    
1:
    # restore the confidential hart's state from memory
    ld	        ra, ({HART_RA_OFFSET})(a0)
    ld	        sp, ({HART_SP_OFFSET})(a0)
    ld	        gp, ({HART_GP_OFFSET})(a0)
    ld	        tp, ({HART_TP_OFFSET})(a0)
    ld	        t0, ({HART_T0_OFFSET})(a0)
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

    # sscratch should contain address of the confidential VM' virtual HART
    csrw        sscratch, a0

    # finally restore from memory the a0 register
    ld	        a0, ({HART_A0_OFFSET})(a0)

    # Make sure that: 
    #   * `mscratch` points to the dump area of this hardware hart
    #   * `sscratch` points to the dump area of the confidential hart assigned to this hardware hart
    mret    