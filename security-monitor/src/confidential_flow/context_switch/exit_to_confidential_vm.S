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

# Restore the confidential VM virtual HART state and return the confidential VM execution. 
# We do not store the security monitor's state because the security monitor is stateless.
# A0 = pointer to VirtualCPU.
.globl exit_to_confidential_vm_asm
.align 4
exit_to_confidential_vm_asm:
    # Should we maintain the mstatus when entering the confidential VM?
	li		    t0, (0b01 << MSTATUS_MPP_SHIFT) | (0b1 << MSTATUS_MPV_SHIFT) | (1 << MSTATUS_MPIE_SHIFT)
	csrw	    mstatus, t0
	# mie (machine interrupt-enable):
    ld	        t0, ({HART_MIE_OFFSET})(a0)
    csrw        mie, t0
    # mip (machine interrupt pending), TODO: expose interrupts
    li          t0, 0
    csrw        mip, t0

    # exception delegation: M->HS (medeleg), HS->VS (hedeleg)
    ld	        t0, ({HART_MEDELEG_OFFSET})(a0)
    csrw        medeleg, t0
    ld	        t0, ({HART_HEDELEG_OFFSET})(a0)
    csrw        hedeleg, t0

    # interrupt delegation: M->HS (mideleg), HS->VS (hideleg)
    ld	        t0, ({HART_MIDELEG_OFFSET})(a0)
    csrw        mideleg, t0
    ld	        t0, ({HART_HIDELEG_OFFSET})(a0)
    csrw        hideleg, t0

    # set the trap vector, so any interrupt invokes the security monitor
    la		    t0, enter_from_confidential_vm_asm
	csrw	    mtvec, t0    
    
	# mepc stores the address of code that will start executing after mret
    ld	        t0, ({HART_MEPC_OFFSET})(a0)
    csrw        mepc, t0

    # restore VS-mode specific CSRs
    ld	        t0, ({HART_VSSTATUS_OFFSET})(a0)
    csrw        vsstatus, t0
    ld	        t0, ({HART_VSIE_OFFSET})(a0)
    csrw        vsie, t0
    ld	        t0, ({HART_VSTVEC_OFFSET})(a0)
    csrw        vstvec, t0
    ld	        t0, ({HART_VSSCRATCH_OFFSET})(a0)
    csrw        vsscratch, t0
    ld	        t0, ({HART_VSEPC_OFFSET})(a0)
    csrw        vsepc, t0
    ld	        t0, ({HART_VSCAUSE_OFFSET})(a0)
    csrw        vscause, t0
    ld	        t0, ({HART_VSTVAL_OFFSET})(a0)
    csrw        vstval, t0
    ld	        t0, ({HART_VSATP_OFFSET})(a0)
    csrw        vsatp, t0

    # restore S-mode specific CSRs
    ld	        t0, ({HART_SSTATUS_OFFSET})(a0)
    csrw        sstatus, t0
    ld	        t0, ({HART_SEPC_OFFSET})(a0)
    csrw        sepc, t0
    # ld	        t0, ({HART_SCOUNTEREN_OFFSET})(a0)
    # csrw        scounteren, t0
    # ld	        t0, ({HART_HVIP_OFFSET})(a0)
    # inject interrupts
    ld	        t0, ({HART_HVIP_OFFSET})(a0)
    csrw        hvip, t0
    ld	        t0, ({HART_HSTATUS_OFFSET})(a0)
    csrw        hstatus, t0


    # check if the fp extension is available before restoring
    # bit 13 and 14 of the sstatus encode this information
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
    # restore from memory the processor state
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

    # the above code must guarantee that:
    # - the mscratch points to the SM's per HART's virtual HART
    # - the sscratch points to the confidential VM's virtual HART
    mret    