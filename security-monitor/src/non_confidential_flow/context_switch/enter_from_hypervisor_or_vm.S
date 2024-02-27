# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
.attribute arch, "rv64gc"
.option norvc
.section .text.init,"ax",@progbits

# Traps on exceptions or interrupts occurring during the hypervisor execution. This is an entry point to the security monitor
#
# Safety: 
#
# The caller must ensure that `mscratch` stores the address of the dump hart area of the currently executing hardware hart. 
.section .text.init
.globl enter_from_hypervisor_or_vm_asm
.align 4
enter_from_hypervisor_or_vm_asm:
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

    csrr        t0, mepc
    sd	        t0, ({HART_MEPC_OFFSET})(sp)
    csrr        t0, mstatus
    sd	        t0, ({HART_MSTATUS_OFFSET})(sp) 

    # Store the original value of `sp`
    csrr	    t0,	mscratch
    sd	        t0, ({HART_SP_OFFSET})(sp)

    # Restore original mscratch so that it points to the per HART vCPU
    csrw        mscratch, sp

    # The security monitor's entry point expects the address of the dumped state of the hardware hart in `a0`
    add         a0, sp, 0

    # Set the stack for this hardware hart
    ld	        sp, ({HART_STACK_ADDRESS_OFFSET})(a0)

    j        enter_from_hypervisor_or_vm