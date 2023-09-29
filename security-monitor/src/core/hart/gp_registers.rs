// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use alloc::vec::Vec;
use core::ops::Range;

#[repr(C)]
pub struct GpRegisters(pub [usize; Self::LEN]);

impl GpRegisters {
    const LEN: usize = 32;

    pub fn empty() -> GpRegisters {
        GpRegisters([0; Self::LEN])
    }

    pub fn clone(&self) -> Self {
        Self(
            GpRegisters::iter()
                .map(|x| self.0[x])
                .collect::<Vec<_>>()
                .try_into()
                .unwrap_or([0; Self::LEN]),
        )
    }

    pub fn set(&mut self, register: GpRegister, value: usize) {
        self.0[register.index()] = value;
    }

    pub fn get(&self, register: GpRegister) -> usize {
        self.0[register.index()]
    }

    pub fn iter() -> Range<usize> {
        Range {
            start: 0,
            end: Self::LEN,
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
#[allow(unused)]
#[allow(non_camel_case_types)]
#[repr(usize)]
pub enum GpRegister {
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

impl GpRegister {
    pub fn index(self) -> usize {
        self as usize
    }

    pub fn from_index(index: usize) -> Option<Self> {
        match index {
            0 => Some(GpRegister::zero),
            1 => Some(GpRegister::ra),
            2 => Some(GpRegister::sp),
            3 => Some(GpRegister::gp),
            4 => Some(GpRegister::tp),
            5 => Some(GpRegister::t0),
            6 => Some(GpRegister::t1),
            7 => Some(GpRegister::t2),
            8 => Some(GpRegister::s0),
            9 => Some(GpRegister::s1),
            10 => Some(GpRegister::a0),
            11 => Some(GpRegister::a1),
            12 => Some(GpRegister::a2),
            13 => Some(GpRegister::a3),
            14 => Some(GpRegister::a4),
            15 => Some(GpRegister::a5),
            16 => Some(GpRegister::a6),
            17 => Some(GpRegister::a7),
            18 => Some(GpRegister::s2),
            19 => Some(GpRegister::s3),
            20 => Some(GpRegister::s4),
            21 => Some(GpRegister::s5),
            22 => Some(GpRegister::s6),
            23 => Some(GpRegister::s7),
            24 => Some(GpRegister::s8),
            25 => Some(GpRegister::s9),
            26 => Some(GpRegister::s10),
            27 => Some(GpRegister::s11),
            28 => Some(GpRegister::t3),
            29 => Some(GpRegister::t4),
            30 => Some(GpRegister::t5),
            31 => Some(GpRegister::t6),
            _ => None,
        }
    }
}
