# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# Restore the hypervisor's CPU state and jump to the hypervisor.
# We do not store SM state because SM is stateless. 
# A0 = pointer to hypervisor's VirtualCPU structure storing HART's state.
.globl exit_to_hypervisor_asm
.align 4
exit_to_hypervisor_asm:
    # the address of the per HART vCPU is in mscratch
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

    # after mret the processor sets the PC to the mepc value
    ld          t0, ({HART_MEPC_OFFSET})(a0)
    csrw        mepc, t0
    ld          t0, ({HART_MSTATUS_OFFSET})(a0)
    csrw        mstatus, t0
    # recover the original state of interrupts
    # ld          t0, ({HART_MIE_OFFSET})(a0)
    # csrw        mie, t0
    # recover the original interrupt/exception delegations
    ld          t0, ({HART_MIDELEG_OFFSET})(a0)
    csrw        mideleg, t0
    ld          t0, ({HART_MEDELEG_OFFSET})(a0)
    csrw        medeleg, t0
    ld          t0, ({HART_HIDELEG_OFFSET})(a0)
    csrw        hideleg, t0
    ld          t0, ({HART_HEDELEG_OFFSET})(a0)
    csrw        hedeleg, t0
    # set the trap vector, so S/VS ecall invokes the security monitor
    la		    t0, enter_from_hypervisor_or_vm_asm
	csrw	    mtvec, t0

    hfence.gvma
    hfence.vvma

    # set hstatus that contains the "supervisor previous virtualization" SPV
    # it is used by the KVM to decide how to handle the trap. 
    ld          t0, ({HART_HSTATUS_OFFSET})(a0)
    csrw        hstatus, t0
    # scause contains the trap's cause
    ld          t0, ({HART_SCAUSE_OFFSET})(a0)
    csrw        scause, t0
    ld          t0, ({HART_STVAL_OFFSET})(a0)
    csrw        stval, t0
    ld          t0, ({HART_SIP_OFFSET})(a0)
    csrw        sip, t0    
    ld          t0, ({HART_SIE_OFFSET})(a0)
    csrw        sie, t0
    # we set up sepc to support VS ecalls.
    # TODO: we must make sure that we never expose real PC of the confidential VM because 
    # we do not want to reveal such information to the hypervisor
    ld          t0, ({HART_SEPC_OFFSET})(a0)
    csrw        sepc, t0
    # htinst used by KVM to learn about inst that caused MMIO trap
    ld          t0, ({HART_HTINST_OFFSET})(a0)
    csrw        htinst, t0
    ld          t0, ({HART_HTVAL_OFFSET})(a0)
    csrw        htval, t0
    # restore the sscratch which is used to temporarly store the address of confidential VM's vCPU
    ld          t0, ({HART_SSCRATCH_OFFSET})(a0)
    csrw        sscratch, t0

    # zeroize VS-mode CSRs: 
    li	        t0, 0
    csrw        vsstatus, t0
    csrw        vsie, t0
    csrw        vstvec, t0
    csrw        vsscratch, t0
    csrw        vsepc, t0
    csrw        vscause, t0
    csrw        vstval, t0
    csrw        vsatp, t0

    # finally restore from memory the t0 and a0 registers
    ld	        t0, ({HART_T0_OFFSET})(a0)
    ld	        a0, ({HART_A0_OFFSET})(a0)

    # the mscratch should contain the address of the per HART vCPU
    # before going back to the hypervisor

    mret    
