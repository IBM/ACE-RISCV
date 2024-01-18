// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_protector::PageSize;
use crate::error::Error;

#[derive(PartialEq)]
pub struct SharePageRequest {
    confidential_vm_virtual_address: ConfidentialVmVirtualAddress,
    page_size: PageSize,
}

impl SharePageRequest {
    pub fn new(address: usize) -> Result<Self, Error> {
        let confidential_vm_virtual_address = ConfidentialVmVirtualAddress(address);
        Ok(Self { confidential_vm_virtual_address, page_size: PageSize::Size4KiB })
    }

    pub fn confidential_vm_virtual_address(&self) -> ConfidentialVmVirtualAddress {
        self.confidential_vm_virtual_address
    }

    pub fn page_size(&self) -> PageSize {
        self.page_size
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct ConfidentialVmVirtualAddress(usize);

impl ConfidentialVmVirtualAddress {
    pub fn usize(&self) -> usize {
        self.0
    }
}

impl core::fmt::Debug for ConfidentialVmVirtualAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[confidential_vm_virtual_address={:x}]", self.0)
    }
}
