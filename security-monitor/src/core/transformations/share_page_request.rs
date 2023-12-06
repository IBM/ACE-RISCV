// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_partitioner::PageSize;
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

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct ConfidentialVmVirtualAddress(usize);

impl ConfidentialVmVirtualAddress {
    pub fn usize(&self) -> usize {
        self.0
    }
}
