// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::error::Error;

/// Defines a range of guest physical addresses that the security monitor interprets as MMIO address and expose load/store operations to the
/// hypervisor. The hypervisor can then emulate them to provide access to virtual devices.
///
/// Confidential VM defines MMIO regions, check COVG ABI for more details.
pub struct ConfidentialVmMmioRegion {
    pub base_address: ConfidentialVmPhysicalAddress,
    pub one_past_the_end_address: ConfidentialVmPhysicalAddress,
}

impl ConfidentialVmMmioRegion {
    pub fn new(start_address: usize, size_in_bytes: usize) -> Result<Self, Error> {
        let base_address = ConfidentialVmPhysicalAddress::new(start_address)?;
        let one_past_the_end_address = base_address.add(size_in_bytes);
        Ok(Self { base_address, one_past_the_end_address })
    }

    pub fn overlaps(&self, other: &Self) -> bool {
        self.base_address < other.one_past_the_end_address && other.base_address < self.one_past_the_end_address
    }

    pub fn contains(&self, other: &Self) -> bool {
        self.base_address <= other.base_address && other.one_past_the_end_address < self.one_past_the_end_address
    }
}
