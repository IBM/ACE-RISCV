// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone)]
pub struct ConfidentialVmId(usize);

impl ConfidentialVmId {
    pub fn new(value: usize) -> Self {
        Self(value)
    }

    pub fn usize(&self) -> usize {
        self.0
    }
}

impl core::fmt::Debug for ConfidentialVmId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "confidential_vm_id={:x}", self.0)
    }
}
