# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

# Disable generation of compressed instructions.
.option norvc

# Define a .text.init section. The .text.init is put at the
# starting address so that the entry _start is put at the RISC-V
# address 0x8000_0000.
.section .text.init

# Execution starts here.
.global _start
_start:
	# Disable linker instruction relaxation for the `la` instruction below.
	# This disallows the assembler from assuming that `gp` is already initialized.
	# This causes the value stored in `gp` to be calculated from `pc`.
	# The job of the global pointer is to give the linker the ability to address
	# memory relative to GP instead of as an absolute address.
.option push
.option norelax
	la		gp, _global_pointer

.option pop
	# Each HART has a SATP (supervisor address translation and protection) register
	# SATP controls MMU, we disable it for now because we don't use virtual memory during the boot process
	# csrw	satp, zero
	# Only hartid=0 bootstraps the system, all other have to sleep and wait for IPI (inter process interrupt)
	# csrr	t0, mhartid
	# bnez	t0, 3f

	# Zero BSS memory section to make sure there is no garbage
	# _bss_start _bss_end are addresses provided by the compiler
	la 		t0, _bss_start
	la		t1, _bss_end
	bgeu	t0, t1, 2f
1:
	sd		zero, (t0)
	addi	t0, t0, 8
	bltu	t0, t1, 1b
2:
	# The stack grows bottom -> top. We set the stack pointer to the end
	la		sp, _stack_end
	# Setting `mstatus` register: 0b01 << 11: Machine's previous protection mode is 2 (MPP=2).
	# bit 7: MPIE (Machine Previous Interrupt Enabler)
	# li		t0, 0b1 << 11 | (1 << 13) # m mde
	# csrw	mstatus, t0	
	li		t0, (1 << 8) | (1 << 5)
	csrw	sstatus, t0	
	# Disable interrupts by setting MIE (machine interrupt-enable) to 0x0 (0x8 would enable it)
	csrw	sie, 0x8
	# We will jump to Rust code, i.e., to the function which name is defined inside MEPC (machine exception program counter)
    # Setting function call arguments (first argument is the mhartid)
    # csrr	a0, mhartid
	la		t1, init
	csrw	sepc, t1
	# la		t2, trap_vector
	# csrw	stvec, t2
	la		ra, waiting_room
	sret

3:
	la		ra, waiting_room
	sret

waiting_room:
	# WFI (wait for interrupt)
	wfi
	j		waiting_room

.global _shutdown
_shutdown:
	li		a7, 0x53525354
	li		a6, 0
	addi	a1, a0, 0
	li		a0, 0
	ecall