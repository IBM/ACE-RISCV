// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{DigestType, MeasurementDigest};
use alloc::vec::Vec;
use core::ops::Range;

#[repr(C)]
pub struct GeneralPurposeRegisters([usize; Self::LEN]);

impl GeneralPurposeRegisters {
    const LEN: usize = 32;

    pub fn empty() -> Self {
        Self([0; Self::LEN])
    }

    pub fn write(&mut self, register: GeneralPurposeRegister, value: usize) {
        self.0[Into::<usize>::into(register)] = value;
    }

    pub fn read(&self, register: GeneralPurposeRegister) -> usize {
        self.0[Into::<usize>::into(register)]
    }

    /// Extends the measurement digest with the context of all GPRs.
    pub fn measure(&self, digest: &mut MeasurementDigest) {
        use sha3::Digest;
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

impl Into<usize> for GeneralPurposeRegister {
    fn into(self) -> usize {
        self as usize
    }
}

impl TryFrom<usize> for GeneralPurposeRegister {
    type Error = crate::error::Error;
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(GeneralPurposeRegister::zero),
            1 => Ok(GeneralPurposeRegister::ra),
            2 => Ok(GeneralPurposeRegister::sp),
            3 => Ok(GeneralPurposeRegister::gp),
            4 => Ok(GeneralPurposeRegister::tp),
            5 => Ok(GeneralPurposeRegister::t0),
            6 => Ok(GeneralPurposeRegister::t1),
            7 => Ok(GeneralPurposeRegister::t2),
            8 => Ok(GeneralPurposeRegister::s0),
            9 => Ok(GeneralPurposeRegister::s1),
            10 => Ok(GeneralPurposeRegister::a0),
            11 => Ok(GeneralPurposeRegister::a1),
            12 => Ok(GeneralPurposeRegister::a2),
            13 => Ok(GeneralPurposeRegister::a3),
            14 => Ok(GeneralPurposeRegister::a4),
            15 => Ok(GeneralPurposeRegister::a5),
            16 => Ok(GeneralPurposeRegister::a6),
            17 => Ok(GeneralPurposeRegister::a7),
            18 => Ok(GeneralPurposeRegister::s2),
            19 => Ok(GeneralPurposeRegister::s3),
            20 => Ok(GeneralPurposeRegister::s4),
            21 => Ok(GeneralPurposeRegister::s5),
            22 => Ok(GeneralPurposeRegister::s6),
            23 => Ok(GeneralPurposeRegister::s7),
            24 => Ok(GeneralPurposeRegister::s8),
            25 => Ok(GeneralPurposeRegister::s9),
            26 => Ok(GeneralPurposeRegister::s10),
            27 => Ok(GeneralPurposeRegister::s11),
            28 => Ok(GeneralPurposeRegister::t3),
            29 => Ok(GeneralPurposeRegister::t4),
            30 => Ok(GeneralPurposeRegister::t5),
            31 => Ok(GeneralPurposeRegister::t6),
            _ => Err(crate::error::Error::InvalidGprId()),
        }
    }
}
