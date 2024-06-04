// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;

/// Defines a range of confidential VM physical address space used for emulated MMIO by the hypervisor.
pub struct ConfidentialVmMmioRegion {
    pub base_address: ConfidentialVmPhysicalAddress,
    pub one_past_the_end_address: ConfidentialVmPhysicalAddress,
}

impl ConfidentialVmMmioRegion {
    pub fn new(start_address: usize, size_in_bytes: usize) -> Self {
        let base_address = ConfidentialVmPhysicalAddress::new(start_address);
        let one_past_the_end_address = base_address.add(size_in_bytes);
        Self { base_address, one_past_the_end_address }
    }

    pub fn overlaps(&self, other: &Self) -> bool {
        self.base_address < other.one_past_the_end_address && other.base_address < self.one_past_the_end_address
    }

    pub fn contains(&self, other: &Self) -> bool {
        self.base_address <= other.base_address && other.one_past_the_end_address < self.one_past_the_end_address
    }
}
