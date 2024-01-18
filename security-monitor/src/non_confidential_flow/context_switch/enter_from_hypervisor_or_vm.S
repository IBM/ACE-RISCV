# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# trap handler from untrusted code to the security monitor
# mscratch stores the pointer to the top of the security monitor's stack
.section .text.init
.globl enter_from_hypervisor_or_vm_asm
.align 4
enter_from_hypervisor_or_vm_asm:
    # address of the per HART vcpu is stored in the mscratch
    csrrw	    sp,	mscratch, sp

    # store current processor state (except for sp) in memory
    sd	        ra, ({HART_RA_OFFSET})(sp)
    # sd	        sp, ({HART_SP_OFFSET})(sp)
    sd	        gp, ({HART_GP_OFFSET})(sp)
    sd	        tp, ({HART_TP_OFFSET})(sp)
    sd	        t0, ({HART_T0_OFFSET})(sp)
    sd	        t1, ({HART_T1_OFFSET})(sp)
    sd	        t2, ({HART_T2_OFFSET})(sp)
    sd	        s0, ({HART_S0_OFFSET})(sp)
    sd	        s1, ({HART_S1_OFFSET})(sp)
    sd	        a0, ({HART_A0_OFFSET})(sp)
    sd	        a1, ({HART_A1_OFFSET})(sp)
    sd	        a2, ({HART_A2_OFFSET})(sp)
    sd	        a3, ({HART_A3_OFFSET})(sp)
    sd	        a4, ({HART_A4_OFFSET})(sp)
    sd	        a5, ({HART_A5_OFFSET})(sp)
    sd	        a6, ({HART_A6_OFFSET})(sp)
    sd	        a7, ({HART_A7_OFFSET})(sp)
    sd	        s2, ({HART_S2_OFFSET})(sp)
    sd	        s3, ({HART_S3_OFFSET})(sp)
    sd	        s4, ({HART_S4_OFFSET})(sp)
    sd	        s5, ({HART_S5_OFFSET})(sp)
    sd	        s6, ({HART_S6_OFFSET})(sp)
    sd	        s7, ({HART_S7_OFFSET})(sp)
    sd	        s8, ({HART_S8_OFFSET})(sp)
    sd	        s9, ({HART_S9_OFFSET})(sp)
    sd	        s10, ({HART_S10_OFFSET})(sp)
    sd	        s11, ({HART_S11_OFFSET})(sp)
    sd	        t3, ({HART_T3_OFFSET})(sp)
    sd	        t4, ({HART_T4_OFFSET})(sp)
    sd	        t5, ({HART_T5_OFFSET})(sp)
    sd	        t6, ({HART_T6_OFFSET})(sp)

    # store M-mode CSRs
    csrr        t0, mepc
    sd	        t0, ({HART_MEPC_OFFSET})(sp)
    csrr        t0, mstatus
    sd	        t0, ({HART_MSTATUS_OFFSET})(sp)
    csrr        t0, mie # needed?
    sd	        t0, ({HART_MIE_OFFSET})(sp)
    csrr        t0, mip # needed?
    sd	        t0, ({HART_MIP_OFFSET})(sp)
    csrr        t0, mideleg
    sd	        t0, ({HART_MIDELEG_OFFSET})(sp)
    csrr        t0, medeleg
    sd	        t0, ({HART_MEDELEG_OFFSET})(sp)
    # we need mtval and mtval2 to support instruction page faults (cause code=20) of regular VMs
    csrr        t0, mtval
    sd	        t0, ({HART_MTVAL_OFFSET})(sp)    
    csrr        t0, mtval2
    sd	        t0, ({HART_MTVAL2_OFFSET})(sp)
    csrr        t0, mtinst
    sd	        t0, ({HART_MTINST_OFFSET})(sp)

    # store VS-mode CSRs
    csrr        t0, vsstatus
    sd	        t0, ({HART_VSSTATUS_OFFSET})(sp)
    csrr        t0, vsie
    sd	        t0, ({HART_VSIE_OFFSET})(sp)
    csrr        t0, vstvec
    sd	        t0, ({HART_VSTVEC_OFFSET})(sp)
    csrr        t0, vsscratch
    sd	        t0, ({HART_VSSCRATCH_OFFSET})(sp)
    csrr        t0, vsepc
    sd	        t0, ({HART_VSEPC_OFFSET})(sp)
    csrr        t0, vscause
    sd	        t0, ({HART_VSCAUSE_OFFSET})(sp)
    csrr        t0, vstval
    sd	        t0, ({HART_VSTVAL_OFFSET})(sp)
    csrr        t0, vsatp
    sd	        t0, ({HART_VSATP_OFFSET})(sp)

    # virtualization related CSRs
    csrr        t0, hgatp
    sd	        t0, ({HART_HGATP_OFFSET})(sp)
    csrr        t0, hvip
    sd	        t0, ({HART_HVIP_OFFSET})(sp)
    csrr        t0, hstatus
    sd	        t0, ({HART_HSTATUS_OFFSET})(sp)
    csrr        t0, hedeleg
    sd	        t0, ({HART_HEDELEG_OFFSET})(sp)
    csrr        t0, hideleg
    sd	        t0, ({HART_HIDELEG_OFFSET})(sp)
    csrr        t0, htinst
    sd	        t0, ({HART_HTINST_OFFSET})(sp)
    csrr        t0, htval
    sd	        t0, ({HART_HTVAL_OFFSET})(sp)

    # store S-mode CSRs
    csrr        t0, sstatus
    sd	        t0, ({HART_SSTATUS_OFFSET})(sp)
    csrr        t0, sepc
    sd	        t0, ({HART_SEPC_OFFSET})(sp)    
    csrr        t0, sip
    sd	        t0, ({HART_SIP_OFFSET})(sp)
    csrr        t0, sie
    sd	        t0, ({HART_SIE_OFFSET})(sp)
    csrr        t0, scause
    sd	        t0, ({HART_SCAUSE_OFFSET})(sp)
    csrr        t0, stval
    sd	        t0, ({HART_STVAL_OFFSET})(sp)
    csrr        t0, sscratch
    sd	        t0, ({HART_SSCRATCH_OFFSET})(sp)

    # now we can store the original sp
    csrr	    t0,	mscratch
    sd	        t0, ({HART_SP_OFFSET})(sp)

    # restore original mscratch so that it points to the per HART vCPU
    csrw        mscratch, sp

    # trap handler expects as a first argument (a0)
    # a pointer to the dumped state of the hart
    add         a0, sp, 0

    # set the stack for this HART
    ld	        sp, ({HART_STACK_ADDRESS_OFFSET})(a0)

    j        enter_from_hypervisor_or_vm