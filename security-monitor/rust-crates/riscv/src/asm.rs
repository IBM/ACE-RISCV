//! Assembly instructions

macro_rules! instruction {
    ($(#[$attr:meta])*, $fnname:ident, $asm:expr) => (
        $(#[$attr])*
        #[inline]
        pub unsafe fn $fnname() {
            match () {
                #[cfg(riscv)]
                () => core::arch::asm!($asm),

                #[cfg(not(riscv))]
                () => unimplemented!(),
            }
        }
    )
}

instruction!(
    /// `nop` instruction wrapper
    ///
    /// Generates a no-operation.  Useful to prevent delay loops from being optimized away.
    , nop, "nop");
instruction!(
    /// `EBREAK` instruction wrapper
    ///
    /// Generates a breakpoint exception.
    , ebreak, "ebreak");
instruction!(
    /// `WFI` instruction wrapper
    ///
    /// Provides a hint to the implementation that the current hart can be stalled until an interrupt might need servicing.
    /// The WFI instruction is just a hint, and a legal implementation is to implement WFI as a NOP.
    , wfi, "wfi");
instruction!(
    /// `SFENCE.VMA` instruction wrapper (all address spaces and page table levels)
    ///
    /// Synchronizes updates to in-memory memory-management data structures with current execution.
    /// Instruction execution causes implicit reads and writes to these data structures; however, these implicit references
    /// are ordinarily not ordered with respect to loads and stores in the instruction stream.
    /// Executing an `SFENCE.VMA` instruction guarantees that any stores in the instruction stream prior to the
    /// `SFENCE.VMA` are ordered before all implicit references subsequent to the `SFENCE.VMA`.
    , sfence_vma_all, "sfence.vma");
instruction!(
    /// `FENCE` instruction wrapper
    ///
    /// The FENCE instruction is used to order device I/O and memory accesses as viewed by other RISC-V
    /// harts and external devices or coprocessors. Any combination of device input (I), device output
    /// (O), memory reads (R), and memory writes (W) may be ordered with respect to any combination
    /// of the same. Informally, no other RISC-V hart or external device can observe any operation in the
    /// successor set following a FENCE before any operation in the predecessor set preceding the FENCE.
    /// Chapter 17 provides a precise description of the RISC-V memory consistency model.
    ///
    /// The FENCE instruction also orders memory reads and writes made by the hart as observed by
    /// memory reads and writes made by an external device. However, FENCE does not order observations
    /// of events made by an external device using any other signaling mechanism.
    , fence, "fence");
instruction!(
    /// `FENCE.I` instruction wrapper
    ///
    /// Used to synchronize the instruction and data streams. RISC-V does not guarantee that
    /// stores to instruction memory will be made visible to instruction fetches on a
    /// RISC-V hart until that hart executes a FENCE.I instruction.
    ///
    /// A FENCE.I instruction ensures that a subsequent instruction fetch on a RISC-V hart
    /// will see any previous data stores already visible to the same RISC-V hart.
    /// FENCE.I does not ensure that other RISC-V harts’ instruction fetches will observe the
    /// local hart’s stores in a multiprocessor system. To make a store to instruction memory
    /// visible to all RISC-V harts, the writing hart also has to execute a data FENCE before
    /// requesting that all remote RISC-V harts execute a FENCE.I.
    ///
    /// The unused fields in the FENCE.I instruction, imm[11:0], rs1, and rd, are reserved for
    /// finer-grain fences in future extensions. For forward compatibility, base
    /// implementations shall ignore these fields, and standard software shall zero these fields.
    , fence_i, "fence.i");

/// `SFENCE.VMA` instruction wrapper
///
/// Synchronizes updates to in-memory memory-management data structures with current execution.
/// Instruction execution causes implicit reads and writes to these data structures; however, these implicit references
/// are ordinarily not ordered with respect to loads and stores in the instruction stream.
/// Executing an `SFENCE.VMA` instruction guarantees that any stores in the instruction stream prior to the
/// `SFENCE.VMA` are ordered before all implicit references subsequent to the `SFENCE.VMA`.
#[inline]
#[allow(unused_variables)]
pub unsafe fn sfence_vma(asid: usize, addr: usize) {
    match () {
        #[cfg(riscv)]
        () => core::arch::asm!("sfence.vma {0}, {1}", in(reg) addr, in(reg) asid),

        #[cfg(not(riscv))]
        () => unimplemented!(),
    }
}

/// Blocks the program for *at least* `cycles` CPU cycles.
///
/// This is implemented in assembly so its execution time is independent of the optimization
/// level, however it is dependent on the specific architecture and core configuration.
///
/// NOTE that the delay can take much longer if interrupts are serviced during its execution
/// and the execution time may vary with other factors. This delay is mainly useful for simple
/// timer-less initialization of peripherals if and only if accurate timing is not essential. In
/// any other case please use a more accurate method to produce a delay.
#[inline]
#[allow(unused_variables)]
pub unsafe fn delay(cycles: u32) {
    match () {
        #[cfg(riscv)]
        () => {
            let real_cyc = 1 + cycles / 2;
            core::arch::asm!(
            "1:",
            "addi {0}, {0}, -1",
            "bne {0}, zero, 1b",
            inout(reg) real_cyc => _,
            options(nomem, nostack),
            )
        }

        #[cfg(not(riscv))]
        () => unimplemented!(),
    }
}
