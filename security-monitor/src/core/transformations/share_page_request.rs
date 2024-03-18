// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::PageSize;
use crate::error::Error;

#[derive(PartialEq)]
pub struct SharePageRequest {
    address: ConfidentialVmPhysicalAddress,
    page_size: PageSize,
}

impl SharePageRequest {
    pub fn new(address: usize) -> Result<Self, Error> {
        Ok(Self { address: ConfidentialVmPhysicalAddress::new(address), page_size: PageSize::Size4KiB })
    }

    pub fn confidential_vm_physical_address(&self) -> ConfidentialVmPhysicalAddress {
        self.address
    }

    pub fn page_size(&self) -> PageSize {
        self.page_size
    }
}
