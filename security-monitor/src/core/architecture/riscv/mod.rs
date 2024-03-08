// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use compressed_instructions::decode_result_register;
pub use floating_point_registers::FloatingPointRegisters;
pub use general_purpose_registers::{GeneralPurposeRegister, GeneralPurposeRegisters};
pub use hart_lifecycle_state::HartLifecycleState;
pub use supervisor_binary_interface::{
    AceExtension, BaseExtension, HsmExtension, IpiExtension, RfenceExtension, SbiExtension, SrstExtension,
};
pub use trap_reason::TrapReason;

mod compressed_instructions;
pub mod control_status_registers;
pub mod fence;
mod floating_point_registers;
mod general_purpose_registers;
pub mod hart_architectural_state;
mod hart_lifecycle_state;
pub mod specification;
mod supervisor_binary_interface;
mod trap_reason;
mod vector_registers;

pub fn put_hart_to_sleep() {
    unsafe {
        core::arch::asm!("wfi");
    }
}
