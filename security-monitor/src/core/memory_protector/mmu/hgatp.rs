// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub struct Hgatp {
    bits: usize,
}

impl Hgatp {
    const HGATP64_MODE_SHIFT: usize = 60;
    const HGATP64_VMID_SHIFT: usize = 44;
    const PAGE_SHIFT: usize = 12;
    const HGATP_PPN_MASK: usize = 0x0000FFFFFFFFFFF;

    pub fn from(bits: usize) -> Self {
        Self { bits }
    }

    pub fn bits(&self) -> usize {
        self.bits
    }

    pub fn address(&self) -> usize {
        (self.bits & Self::HGATP_PPN_MASK) << Self::PAGE_SHIFT
    }

    pub fn mode(&self) -> Option<HgatpMode> {
        HgatpMode::from_code((self.bits >> Self::HGATP64_MODE_SHIFT) & 0b1111)
    }

    pub fn new(address: usize, mode: HgatpMode, vmid: usize) -> Self {
        let ppn = (address >> Self::PAGE_SHIFT) & Self::HGATP_PPN_MASK;
        Self { bits: (vmid << Self::HGATP64_VMID_SHIFT) | (mode.code() << Self::HGATP64_MODE_SHIFT) | ppn }
    }
}

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
