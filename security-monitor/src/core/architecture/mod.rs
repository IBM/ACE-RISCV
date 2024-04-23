// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use riscv::control_status_registers::*;
pub use riscv::fence::*;
pub use riscv::hart_architectural_state::*;
pub use riscv::*;

mod riscv;

#[inline]
pub fn is_bit_enabled(register_value: usize, bit_index: usize) -> bool {
    are_bits_enabled(register_value, 1 << bit_index)
}

#[inline]
pub fn are_bits_enabled(register_value: usize, bit_mask: usize) -> bool {
    register_value & bit_mask > 0
}
