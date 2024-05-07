// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
use alloc::vec::Vec;
use core::ops::Range;

#[repr(C)]
pub struct FloatingPointRegisters(pub [usize; Self::LEN]);

impl FloatingPointRegisters {
    const LEN: usize = 32;

    pub fn clone(&self) -> Self {
        Self(FloatingPointRegisters::iter().map(|x| self.0[x]).collect::<Vec<_>>().try_into().unwrap_or([0; Self::LEN]))
    }

    pub fn empty() -> FloatingPointRegisters {
        FloatingPointRegisters([0; Self::LEN])
    }

    pub fn iter() -> Range<usize> {
        Range { start: 0, end: Self::LEN }
    }

    pub fn save_in_main_memory(&mut self) {
        unsafe {
            core::arch::asm!("fsd f0, 0({val})", val = in(reg) self);
            // core::arch::asm!("fsd f1, {val}", val = in(reg) self.0[1]);
        }
    }

    pub fn restore_from_main_memory(&self) {}
}
