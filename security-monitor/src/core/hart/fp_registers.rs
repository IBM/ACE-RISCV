// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use alloc::vec::Vec;
use core::ops::Range;

#[repr(C)]
pub struct FpRegisters(pub [usize; Self::LEN]);

impl FpRegisters {
    const LEN: usize = 32;

    pub fn clone(&self) -> Self {
        Self(FpRegisters::iter().map(|x| self.0[x]).collect::<Vec<_>>().try_into().unwrap_or([0; Self::LEN]))
    }

    pub fn empty() -> FpRegisters {
        FpRegisters([0; Self::LEN])
    }

    pub fn iter() -> Range<usize> {
        Range { start: 0, end: Self::LEN }
    }
}
