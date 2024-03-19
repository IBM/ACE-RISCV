// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::error::Error;

#[derive(PartialEq)]
pub struct UnsharePageRequest {
    address: ConfidentialVmPhysicalAddress,
}

impl UnsharePageRequest {
    pub fn new(address: usize) -> Result<Self, Error> {
        Ok(Self { address: ConfidentialVmPhysicalAddress::new(address) })
    }

    pub fn address(&self) -> &ConfidentialVmPhysicalAddress {
        &self.address
    }
}
