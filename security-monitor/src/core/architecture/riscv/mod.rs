// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
pub use compressed_instructions::decode_result_register;
pub use floating_point_registers::FloatingPointRegisters;
pub use general_purpose_registers::{GeneralPurposeRegister, GeneralPurposeRegisters};
pub use hart_lifecycle_state::HartLifecycleState;
pub use supervisor_binary_interface::{
    AceExtension, BaseExtension, HsmExtension, IpiExtension, RfenceExtension, SbiExtension, SrstExtension,
};
pub use trap_cause::TrapCause;

mod compressed_instructions;
pub mod control_status_registers;
pub mod fence;
mod floating_point_registers;
mod general_purpose_registers;
pub mod hart_architectural_state;
mod hart_lifecycle_state;
pub mod specification;
mod supervisor_binary_interface;
mod trap_cause;
mod vector_registers;

pub fn put_hart_to_sleep() {
    unsafe {
        core::arch::asm!("wfi");
    }
}

#[inline]
pub fn enable_bit(register_value: &mut usize, bit_index: usize) {
    enable_bits(register_value, 1 << bit_index);
}

#[inline]
pub fn enable_bits(register_value: &mut usize, bit_mask: usize) {
    *register_value |= bit_mask;
}

#[inline]
pub fn disable_bit(register_value: &mut usize, bit_index: usize) {
    disable_bits(register_value, 1 << bit_index);
}

#[inline]
pub fn disable_bits(register_value: &mut usize, bit_mask: usize) {
    *register_value &= !bit_mask;
}

#[inline]
pub fn is_bit_enabled(register_value: usize, bit_index: usize) -> bool {
    are_bits_enabled(register_value, 1 << bit_index)
}

#[inline]
pub fn are_bits_enabled(register_value: usize, bit_mask: usize) -> bool {
    register_value & bit_mask > 0
}
