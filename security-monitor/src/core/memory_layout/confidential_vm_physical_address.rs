// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;

#[derive(PartialEq, PartialOrd, Clone, Copy)]
pub struct ConfidentialVmPhysicalAddress(usize);

impl ConfidentialVmPhysicalAddress {
    pub fn new(confidential_vm_physical_address: usize) -> Result<Self, Error> {
        if confidential_vm_physical_address == 0 {
            Err(Error::InvalidParameter())
        } else {
            Ok(Self(confidential_vm_physical_address))
        }
    }

    pub fn add(&self, offset: usize) -> Self {
        Self(self.0 + offset)
    }

    pub fn usize(&self) -> usize {
        self.0
    }

    pub fn is_aligned_to(&self, align: usize) -> bool {
        self.0 % align == 0
    }
}

impl core::fmt::Debug for ConfidentialVmPhysicalAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "0x{:x}", self.0)
    }
}
