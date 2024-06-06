// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[repr(C)]
pub struct FloatingPointRegisters(pub [usize; Self::LEN]);

impl FloatingPointRegisters {
    const LEN: usize = 32;

    pub fn empty() -> Self {
        Self([0; Self::LEN])
    }

    pub fn save_in_main_memory(&mut self) {
        // TODO: replace with macro!
        // unsafe {
        //     core::arch::asm!("fsd f0, 0({val})", val = in(reg) self.0[0]);
        // }
    }

    pub fn restore_from_main_memory(&mut self) {
        // TODO: replace with macro!
        unsafe {}
    }
}
