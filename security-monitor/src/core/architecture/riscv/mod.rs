// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
pub use control_status_registers::{ControlStatusRegister, ControlStatusRegisters, CSR};
pub use extensions::compressed_instructions::decode_result_register;
pub use extensions::floating_point_unit::FloatingPointUnit;
pub use extensions::supervisor_timer_extension::SupervisorTimerExtension;
pub use extensions::HardwareExtension;
pub use general_purpose_registers::{GeneralPurposeRegister, GeneralPurposeRegisters};
pub use hart_architectural_state::HartArchitecturalState;
pub use hart_lifecycle_state::HartLifecycleState;
pub use mmu::{Hgatp, PageSize, SharedPage};
pub use trap_cause::TrapCause;

pub mod fence;
pub mod hart_architectural_state;
pub mod iopmp;
pub mod mmu;
pub mod pmp;
pub mod sbi;
pub mod specification;
pub mod tlb;

mod control_status_registers;
mod extensions;
mod general_purpose_registers;
mod hart_lifecycle_state;
mod trap_cause;

pub fn put_hart_to_sleep() {
    // careful: if interrupts are disabled, this hart will never trap
    unsafe {
        core::arch::asm!("wfi");
    }
}
