// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialVmVirtualAddress;
use crate::error::Error;

#[derive(PartialEq)]
pub struct UnsharePageRequest {
    confidential_vm_virtual_address: ConfidentialVmVirtualAddress,
}

impl UnsharePageRequest {
    pub fn new(address: usize) -> Result<Self, Error> {
        let confidential_vm_virtual_address = ConfidentialVmVirtualAddress::new(address);
        Ok(Self { confidential_vm_virtual_address })
    }

    pub fn confidential_vm_virtual_address(&self) -> ConfidentialVmVirtualAddress {
        self.confidential_vm_virtual_address
    }
}