# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# Performs the context switch between two security domains further refered to as `previous security domain` and `next security domain`.
#
# a0 is the address of the previous security domain
# a1 is the address of the next security domain
.section .text.init
.globl switch_security_domains_asm
switch_security_domains_asm:
    # First, we dump the state of the old security domain to its location in the memory pointed by the `a0` register.
    # We do not need to dump the processor state that has already been dumped when entering the security monitor, i.e., gprs.
    # We do not store/load xip registers

    # store M-mode CSRs
    csrr        t0, mepc
    sd	        t0, ({HART_MEPC_OFFSET})(a0)
    csrr        t0, mstatus
    sd	        t0, ({HART_MSTATUS_OFFSET})(a0)
    csrr        t0, mie # needed?
    sd	        t0, ({HART_MIE_OFFSET})(a0)
    # csrr        t0, mip # needed?
    # sd	        t0, ({HART_MIP_OFFSET})(a0)
    csrr        t0, mideleg
    sd	        t0, ({HART_MIDELEG_OFFSET})(a0)
    csrr        t0, medeleg
    sd	        t0, ({HART_MEDELEG_OFFSET})(a0)
    # we need mtval and mtval2 to support instruction page faults (cause code=20) of regular VMs
    csrr        t0, mtval
    sd	        t0, ({HART_MTVAL_OFFSET})(a0)    
    csrr        t0, mtval2
    sd	        t0, ({HART_MTVAL2_OFFSET})(a0)
    csrr        t0, mtinst
    sd	        t0, ({HART_MTINST_OFFSET})(a0)
    csrr        t0, mtvec
    sd	        t0, ({HART_MTVEC_OFFSET})(a0)

    # virtualization related CSRs
    csrr        t0, hgatp
    sd	        t0, ({HART_HGATP_OFFSET})(a0)
    csrr        t0, hvip
    sd	        t0, ({HART_HVIP_OFFSET})(a0)
    csrr        t0, hgeip
    sd	        t0, ({HART_HGEIP_OFFSET})(a0)    
    csrr        t0, hie
    sd	        t0, ({HART_HIE_OFFSET})(a0)
    csrr        t0, hstatus
    sd	        t0, ({HART_HSTATUS_OFFSET})(a0)
    csrr        t0, hedeleg
    sd	        t0, ({HART_HEDELEG_OFFSET})(a0)
    csrr        t0, hideleg
    sd	        t0, ({HART_HIDELEG_OFFSET})(a0)
    csrr        t0, htinst
    sd	        t0, ({HART_HTINST_OFFSET})(a0)
    csrr        t0, htval
    sd	        t0, ({HART_HTVAL_OFFSET})(a0) 
    csrr        t0, vstimecmp
    sd	        t0, ({HART_VSTIMECMP_OFFSET})(a0)
    csrr        t0, htimedelta
    sd	        t0, ({HART_HTIMEDELTA_OFFSET})(a0)    

    # store S-mode CSRs
    csrr        t0, sstatus
    sd	        t0, ({HART_SSTATUS_OFFSET})(a0)
    csrr        t0, sepc
    sd	        t0, ({HART_SEPC_OFFSET})(a0)
    # csrr        t0, sip
    # sd	        t0, ({HART_SIP_OFFSET})(a0)
    csrr        t0, sie
    sd	        t0, ({HART_SIE_OFFSET})(a0)
    csrr        t0, scause
    sd	        t0, ({HART_SCAUSE_OFFSET})(a0)
    csrr        t0, stval
    sd	        t0, ({HART_STVAL_OFFSET})(a0)
    csrr        t0, sscratch
    sd	        t0, ({HART_SSCRATCH_OFFSET})(a0)
    csrr        t0, stvec
    sd	        t0, ({HART_STVEC_OFFSET})(a0)
    csrr        t0, scounteren
    sd	        t0, ({HART_SCOUNTEREN_OFFSET})(a0)

    # store VS-mode CSRs
    csrr        t0, vsstatus
    sd	        t0, ({HART_VSSTATUS_OFFSET})(a0)
    csrr        t0, vsie
    sd	        t0, ({HART_VSIE_OFFSET})(a0)
    csrr        t0, vsip
    sd	        t0, ({HART_VSIP_OFFSET})(a0)    
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

    ###
    # Now, let's load the state of the next security domain
    # We do not dump the processor state that might change as part of the security monitor's execution, i.e., gprs. 
    # This state will be dumped when switching context from the security monitor to the next security domain.

    # load M-mode registers
    ld          t0, ({HART_MEPC_OFFSET})(a1)
    csrw        mepc, t0
    ld          t0, ({HART_MSTATUS_OFFSET})(a1)
    csrw        mstatus, t0
    ld          t0, ({HART_MIE_OFFSET})(a1)
    csrw        mie, t0
    # ld          t0, ({HART_MIP_OFFSET})(a1)
    # csrw        mip, t0
    ld          t0, ({HART_MIDELEG_OFFSET})(a1)
    csrw        mideleg, t0
    ld          t0, ({HART_MEDELEG_OFFSET})(a1)
    csrw        medeleg, t0
    ld          t0, ({HART_MTVAL_OFFSET})(a1)
    csrw        mtval, t0
    ld          t0, ({HART_MTVAL2_OFFSET})(a1)
    csrw        mtval2, t0
    ld          t0, ({HART_MTINST_OFFSET})(a1)
    csrw        mtinst, t0
    ld          t0, ({HART_MTVEC_OFFSET})(a1)
    csrw        mtvec, t0
    
    # restore S-mode specific CSRs
    ld	        t0, ({HART_SSTATUS_OFFSET})(a1)
    csrw        sstatus, t0
    ld	        t0, ({HART_SEPC_OFFSET})(a1)
    csrw        sepc, t0
    # ld	        t0, ({HART_SIP_OFFSET})(a1)
    # csrw        sip, t0
    ld          t0, ({HART_SIE_OFFSET})(a1)
    csrw        sie, t0    
    ld          t0, ({HART_SCAUSE_OFFSET})(a1)
    csrw        scause, t0    
    ld          t0, ({HART_STVAL_OFFSET})(a1)
    csrw        stval, t0
    ld          t0, ({HART_SSCRATCH_OFFSET})(a1)
    csrw        sscratch, t0
    ld          t0, ({HART_STVEC_OFFSET})(a1)
    csrw        stvec, t0
    ld	        t0, ({HART_SCOUNTEREN_OFFSET})(a1)
    csrw        scounteren, t0

    # HS-mode related CSRs
    ld	        t0, ({HART_HGATP_OFFSET})(a1)
    csrw        hgatp, t0
    ld	        t0, ({HART_HSTATUS_OFFSET})(a1)
    csrw        hstatus, t0    
    ld	        t0, ({HART_HVIP_OFFSET})(a1)
    csrw        hvip, t0
    ## CAREFUL WITH HGEIP
    # ld	        t0, ({HART_HGEIP_OFFSET})(a1)
    # csrw        hgeip, t0
    ld          t0, ({HART_HIDELEG_OFFSET})(a1)
    csrw        hideleg, t0
    ld          t0, ({HART_HEDELEG_OFFSET})(a1)
    csrw        hedeleg, t0
    ld          t0, ({HART_HIE_OFFSET})(a1)
    csrw        hie, t0
    ld          t0, ({HART_HTINST_OFFSET})(a1)
    csrw        htinst, t0
    ld          t0, ({HART_HTVAL_OFFSET})(a1)
    csrw        htval, t0
    # timer-related registers
    # vstimecmp is introduces as part of the Zstc extension
    ld	        t0, ({HART_VSTIMECMP_OFFSET})(a1)
    csrw        vstimecmp, t0
    ld	        t0, ({HART_HTIMEDELTA_OFFSET})(a1)
    csrw        htimedelta, t0

    # restore VS-mode specific CSRs
    ld	        t0, ({HART_VSSTATUS_OFFSET})(a1)
    csrw        vsstatus, t0
    ld	        t0, ({HART_VSIE_OFFSET})(a1)
    csrw        vsie, t0
    ld	        t0, ({HART_VSIP_OFFSET})(a1)
    csrw        vsip, t0
    ld	        t0, ({HART_VSTVEC_OFFSET})(a1)
    csrw        vstvec, t0
    ld	        t0, ({HART_VSSCRATCH_OFFSET})(a1)
    csrw        vsscratch, t0
    ld	        t0, ({HART_VSEPC_OFFSET})(a1)
    csrw        vsepc, t0
    ld	        t0, ({HART_VSCAUSE_OFFSET})(a1)
    csrw        vscause, t0
    ld	        t0, ({HART_VSTVAL_OFFSET})(a1)
    csrw        vstval, t0
    ld	        t0, ({HART_VSATP_OFFSET})(a1)
    csrw        vsatp, t0

    # clear microarchitectural state. Below instructions might have already been executed by the memory protector component.
    hfence.gvma
    hfence.vvma

    ret
