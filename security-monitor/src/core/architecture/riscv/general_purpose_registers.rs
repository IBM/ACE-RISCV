// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{DigestType, MeasurementDigest};
use alloc::vec::Vec;
use core::ops::Range;

#[repr(C)]
pub struct GeneralPurposeRegisters(pub [usize; Self::LEN]);

impl GeneralPurposeRegisters {
    const LEN: usize = 32;

    pub fn empty() -> Self {
        Self([0; Self::LEN])
    }

    pub fn clone(&self) -> Self {
        Self(Self::iter().map(|x| self.0[x]).collect::<Vec<_>>().try_into().unwrap_or([0; Self::LEN]))
    }

    pub fn write(&mut self, register: GeneralPurposeRegister, value: usize) {
        self.0[register.index()] = value;
    }

    pub fn read(&self, register: GeneralPurposeRegister) -> usize {
        self.0[register.index()]
    }

    /// Extends the measurement digest with the context of all GPRs.
    pub fn measure(&self, digest: &mut MeasurementDigest) {
        use sha2::Digest;
        let mut hasher = DigestType::new_with_prefix(digest.clone());
        self.0.iter().for_each(|gpr_value| hasher.update(gpr_value.to_le_bytes()));
        hasher.finalize_into(digest);
    }

    pub fn iter() -> Range<usize> {
        Range { start: 0, end: Self::LEN }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
#[allow(unused)]
#[allow(non_camel_case_types)]
#[repr(usize)]
pub enum GeneralPurposeRegister {
    zero = 0,
    ra,
    sp,
    gp,
    tp,
    t0,
    t1,
    t2,
    s0,
    s1,
    a0,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    s2,
    s3,
    s4,
    s5,
    s6,
    s7,
    s8,
    s9,
    s10,
    s11,
    t3,
    t4,
    t5,
    t6,
}

impl GeneralPurposeRegister {
    pub fn index(self) -> usize {
        self as usize
    }

    pub fn from_index(index: usize) -> Option<Self> {
        match index {
            0 => Some(GeneralPurposeRegister::zero),
            1 => Some(GeneralPurposeRegister::ra),
            2 => Some(GeneralPurposeRegister::sp),
            3 => Some(GeneralPurposeRegister::gp),
            4 => Some(GeneralPurposeRegister::tp),
            5 => Some(GeneralPurposeRegister::t0),
            6 => Some(GeneralPurposeRegister::t1),
            7 => Some(GeneralPurposeRegister::t2),
            8 => Some(GeneralPurposeRegister::s0),
            9 => Some(GeneralPurposeRegister::s1),
            10 => Some(GeneralPurposeRegister::a0),
            11 => Some(GeneralPurposeRegister::a1),
            12 => Some(GeneralPurposeRegister::a2),
            13 => Some(GeneralPurposeRegister::a3),
            14 => Some(GeneralPurposeRegister::a4),
            15 => Some(GeneralPurposeRegister::a5),
            16 => Some(GeneralPurposeRegister::a6),
            17 => Some(GeneralPurposeRegister::a7),
            18 => Some(GeneralPurposeRegister::s2),
            19 => Some(GeneralPurposeRegister::s3),
            20 => Some(GeneralPurposeRegister::s4),
            21 => Some(GeneralPurposeRegister::s5),
            22 => Some(GeneralPurposeRegister::s6),
            23 => Some(GeneralPurposeRegister::s7),
            24 => Some(GeneralPurposeRegister::s8),
            25 => Some(GeneralPurposeRegister::s9),
            26 => Some(GeneralPurposeRegister::s10),
            27 => Some(GeneralPurposeRegister::s11),
            28 => Some(GeneralPurposeRegister::t3),
            29 => Some(GeneralPurposeRegister::t4),
            30 => Some(GeneralPurposeRegister::t5),
            31 => Some(GeneralPurposeRegister::t6),
            _ => None,
        }
    }
}
