.option norvc
.altmacro
.set NUM_GP_REGS, 32  # Number of registers per hart
.set REG_SIZE, 8   # Register size (in bytes)

# Use macros for saving and restoring multiple registers
.macro save_gp i, basereg=t6
	sd	x\i, ((\i)*REG_SIZE)(\basereg)
.endm
.macro load_gp i, basereg=t6
	ld	x\i, ((\i)*REG_SIZE)(\basereg)
.endm

.section .text
.global trap_handler_asm
.align 4
trap_handler_asm:
	csrrw	t6, sscratch, t6
	.set 	i, 1
	.rept	30
		save_gp	%i
		.set	i, i+1
	.endr

	# store the trap frame address in t5 so that we can store it in sscratch later
	mv		t5, t6
	# now it is time to store in the memory the last register x31, i.e., t6. Its original value is in sscratch
	csrr	t6, sscratch
	save_gp 31, t6
	# store back the trap frame address in sscratch, otherwise we will break the context switch procedure
	csrw	sscratch, t5

	# now its time to load some CSRs into arguments of the trap_handler function
	csrr	a0, sepc
	csrr	a1, stval
	csrr	a2, scause
	# careful! the stack might not be set, so 'call' instruction will fail
	j 		trap_handler

	# we returned from the trap handler procedure. It is time to prepare to resume execution of the interrupted code
	# a0 (returned value from the trap handler) should contain the address of the instruction to resume
	csrw	sepc, a0
	# lets restore the original processor state from memory. The address of the dumped trap frame is in sscratch
	csrr	t6, sscratch
	.set	i, 1
	.rept	31
		load_gp %i
		.set	i, i+1
	.endr

	sret	
