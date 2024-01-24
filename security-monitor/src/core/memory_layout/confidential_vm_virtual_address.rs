// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Clone, Copy)]
pub struct ConfidentialVmVirtualAddress(usize);

impl ConfidentialVmVirtualAddress {
    pub fn new(address: usize) -> Self {
        Self(address)
    }

    pub fn usize(&self) -> usize {
        self.0
    }
}

impl core::fmt::Debug for ConfidentialVmVirtualAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "confidential_vm_virtual_address={:x}", self.0)
    }
}
