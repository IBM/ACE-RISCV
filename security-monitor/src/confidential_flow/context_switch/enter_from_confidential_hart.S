# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# This is the trap vector that gets executed on any interrupt or confidential VM-driven exception.
# The trap vector address must be 4B aligned according to the spec.
.globl enter_from_confidential_hart_asm
.align 4
enter_from_confidential_hart_asm:
    csrrw	    a0,	sscratch, a0
    # store current processor state (except for a0) in memory
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

    # check if the fp extension is available before restoring
    # bit 13 and 14 of the sstatus encode this information
    sd          t0, ({HART_SSTATUS_OFFSET})(a0)
    sra         t0, t0, 13
    add         t0, t0, 0b11
    beqz	    t0, 1f
    # store the float pointing registers
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
    # store VS-mode related CSRs
    csrr        t0, vsstatus
    sd	        t0, ({HART_VSSTATUS_OFFSET})(a0)
    csrr        t0, vsie
    sd	        t0, ({HART_VSIE_OFFSET})(a0)
    csrr        t0, vstvec
    sd	        t0, ({HART_VSTVEC_OFFSET})(a0)
    csrr        t0, vsscratch
    sd	        t0, ({HART_VSSCRATCH_OFFSET})(a0)
    csrr        t0, vsepc
    sd	        t0, ({HART_VSEPC_OFFSET})(a0)
    csrr        t0, vscause
    sd	        t0, ({HART_VSCAUSE_OFFSET})(a0)
    csrr        t0, vstval
    sd	        t0, ({HART_VSTVAL_OFFSET})(a0)
    csrr        t0, vsatp
    sd	        t0, ({HART_VSATP_OFFSET})(a0)

    # virtualization-related CSRs
    csrr        t0, hvip
    sd	        t0, ({HART_HVIP_OFFSET})(a0)
    csrr        t0, hstatus
    sd	        t0, ({HART_HSTATUS_OFFSET})(a0)

    # S-mode related CSRs
    csrr        t0, sstatus
    sd	        t0, ({HART_SSTATUS_OFFSET})(a0)
    csrr        t0, scounteren
    sd	        t0, ({HART_SCOUNTEREN_OFFSET})(a0)
    csrr        t0, sepc    # not needed?
    sd	        t0, ({HART_SEPC_OFFSET})(a0)

    # store the address of the instruction at which trap occured
    csrr        t0, mepc
    sd	        t0, ({HART_MEPC_OFFSET})(a0)
    csrr        t0, mtinst
    sd	        t0, ({HART_MTINST_OFFSET})(a0)    
    csrr        t0, mtval
    sd	        t0, ({HART_MTVAL_OFFSET})(a0)    
    csrr        t0, mtval2
    sd	        t0, ({HART_MTVAL2_OFFSET})(a0)    

    # now we can store the original a0
    csrr        t0, sscratch
    sd	        t0, ({HART_A0_OFFSET})(a0)

    # recover the stack pointer for this HART
    # the mscratch stores the address of the data 
    # structure storing dumped HART state
    csrr        a0, mscratch
    ld	        sp, ({HART_STACK_ADDRESS_OFFSET})(a0)

    # mscratch must point to the per HART data structure
    # sscratch must point to the confidential VM's vHART data structure
    # first argument (a0) must point to the dumped hart memory area
    # TODO: Prove that we don't violate C calling conventions and parameters 
    # are correctly passed.
    j        enter_from_confidential_hart
