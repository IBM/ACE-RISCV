// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use compressed_instructions::decode_result_register;
pub use floating_point_registers::FloatingPointRegisters;
pub use general_purpose_registers::{GeneralPurposeRegister, GeneralPurposeRegisters};
pub use hart_architectural_state::HartArchitecturalState;
pub use hart_lifecycle_state::HartLifecycleState;
pub use sbi::{AceExtension, BaseExtension, HsmExtension, IpiExtension, RfenceExtension, SbiExtension, SrstExtension};
pub use trap_reason::TrapReason;

mod compressed_instructions;
pub mod csr;
pub mod fence;
mod floating_point_registers;
mod general_purpose_registers;
mod hart_architectural_state;
mod hart_lifecycle_state;
mod sbi;
pub mod specification;
mod trap_reason;
mod vector_registers;

pub fn put_hart_to_sleep() {
    unsafe {
        core::arch::asm!("wfi");
    }
}
