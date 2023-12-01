// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_tracker::NonConfidentialMemoryAddress;
use crate::core::mmu::PageSize;
use crate::core::transformations::{ConfidentialVmVirtualAddress, SharePageRequest};
use crate::error::Error;

pub struct SharedPage {
    hypervisor_address: NonConfidentialMemoryAddress,
    confidential_vm_virtual_address: ConfidentialVmVirtualAddress,
    page_size: PageSize,
}

impl SharedPage {
    pub fn new(hypervisor_address: usize, request: SharePageRequest) -> Result<Self, Error> {
        let page_size = request.page_size();
        let hypervisor_end_address = hypervisor_address + page_size.in_bytes() - 1;

        // Security: check that the start address is located in the non-confidential memory
        let hypervisor_address = NonConfidentialMemoryAddress::new(hypervisor_address)?;
        // Security: check that the end address is located in the non-confidential memory
        NonConfidentialMemoryAddress::new(hypervisor_end_address)?;

        let confidential_vm_virtual_address = request.confidential_vm_virtual_address();

        Ok(Self { hypervisor_address, confidential_vm_virtual_address, page_size })
    }

    pub fn into_hypervisor_address(self) -> NonConfidentialMemoryAddress {
        self.hypervisor_address
    }

    pub fn confidential_vm_virtual_address(&self) -> ConfidentialVmVirtualAddress {
        self.confidential_vm_virtual_address
    }
}
