// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use super::specification::*;

#[repr(usize)]
#[derive(Clone, Copy, Debug)]
pub enum HgatpMode {
    Sv57x4 = 10,
}

impl HgatpMode {
    fn code(self) -> usize {
        self as usize
    }

    fn from_code(code: usize) -> Option<Self> {
        match code {
            10 => Some(HgatpMode::Sv57x4),
            _ => None,
        }
    }
}

#[derive(PartialEq)]
pub struct Hgatp(usize);

impl Hgatp {
    pub fn new(address: usize, mode: HgatpMode, vmid: usize) -> Self {
        Self((vmid << HGATP64_VMID_SHIFT) | (mode.code() << HGATP64_MODE_SHIFT) | (address >> HGATP_PAGE_SHIFT) & HGATP_PPN_MASK)
    }

    pub fn disabled() -> Self {
        Self::from(0)
    }

    pub fn from(bits: usize) -> Self {
        Self(bits)
    }

    pub fn bits(&self) -> usize {
        self.0
    }

    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }

    pub fn root_page_table_pointer(&self) -> *mut usize {
        ((self.0 & HGATP_PPN_MASK) << HGATP_PAGE_SHIFT) as *mut usize
    }

    pub fn mode(&self) -> Option<HgatpMode> {
        HgatpMode::from_code((self.0 >> HGATP64_MODE_SHIFT) & 0b1111)
    }
}
