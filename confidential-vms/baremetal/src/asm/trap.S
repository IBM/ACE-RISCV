.option norvc
.altmacro
.set NUM_GP_REGS, 32  # Number of registers per hart
.set NUM_FP_REGS, 32
.set REG_SIZE, 8   # Register size (in bytes)
.set MAX_CPUS, 4   # Maximum number of CPUs

# Use macros for saving and restoring multiple registers
.macro save_gp i, basereg=t6
	sd	x\i, ((\i)*REG_SIZE)(\basereg)
.endm
.macro load_gp i, basereg=t6
	ld	x\i, ((\i)*REG_SIZE)(\basereg)
.endm
.macro save_fp i, basereg=t6
	fsd	f\i, ((NUM_GP_REGS+(\i))*REG_SIZE)(\basereg)
.endm
.macro load_fp i, basereg=t6
	fld	f\i, ((NUM_GP_REGS+(\i))*REG_SIZE)(\basereg)
.endm

.section .text
.global trap_vector
.align 4
trap_vector:
	csrrw	t6, sscratch, t6
	.set 	i, 1
	.rept	30
		save_gp	%i
		.set	i, i+1
	.endr

	mv		t5, t6
	csrr	t6, sscratch
	save_gp 31, t5

	csrw	mscratch, t5

	csrr	a0, sepc
	csrr	a1, stval
	csrr	a2, scause
	csrr	a3, 0x0 #mhartid
	csrr	a4, sstatus
	mv		a5, t5
	# ld		sp, 520(a5)
	call	trap_handler

	csrw	sepc, a0

	csrr	t6, sscratch

	.set	i, 1
	.rept	31
		load_gp %i
		.set	i, i+1
	.endr

	sret	
