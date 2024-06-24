// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use riscv::*;

pub mod riscv;

#[inline]
pub fn is_bit_enabled(register_value: usize, bit_index: usize) -> bool {
    register_value & (1 << bit_index) > 0
}
