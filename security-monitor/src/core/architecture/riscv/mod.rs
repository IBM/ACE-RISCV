// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
pub use compressed_instructions::decode_result_register;
pub use floating_point_registers::FloatingPointRegisters;
pub use general_purpose_registers::{GeneralPurposeRegister, GeneralPurposeRegisters};
pub use hart_lifecycle_state::HartLifecycleState;
pub use nacl_shared_memory::NaclSharedMemory;
pub use supervisor_binary_interface::{
    AceExtension, BaseExtension, CovgExtension, CovhExtension, CoviExtension, HsmExtension, IpiExtension, NaclExtension, RfenceExtension,
    SbiExtension, SrstExtension,
};
pub use trap_cause::TrapCause;

pub mod control_status_registers;
pub mod fence;
pub mod hart_architectural_state;
pub mod specification;

mod compressed_instructions;
mod floating_point_registers;
mod general_purpose_registers;
mod hart_lifecycle_state;
mod nacl_shared_memory;
mod supervisor_binary_interface;
mod trap_cause;
mod vector_registers;

pub fn put_hart_to_sleep() {
    unsafe {
        core::arch::asm!("wfi");
    }
}
