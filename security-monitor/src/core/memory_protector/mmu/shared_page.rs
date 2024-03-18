// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::{ConfidentialVmPhysicalAddress, MemoryLayout, NonConfidentialMemoryAddress};
use crate::core::memory_protector::PageSize;
use crate::error::Error;

/// `SharedPage` stores internally a raw pointer to an address in non-confidential memory that the shared page
/// is associated to. Referencing this non-confidential memory from the security monitor is unsafe because we
/// cannot guarantee that two concurrent hardware threads are not writting to it at the same time. This is because
/// the non-confidential memory is owned by the untrusted code (hypervisor). Thus, we must ensure the security monitor
/// never dereferences this raw pointer, or if it must to do so, it must use atomic read/write to make sure that
/// hardware ensures synchronized access to these memory locations.
pub struct SharedPage {
    pub hypervisor_address: NonConfidentialMemoryAddress,
    pub confidential_vm_address: ConfidentialVmPhysicalAddress,
    pub size: PageSize,
}

/// It is safe to implement Send+Sync on the SharedPage type because it encapsulates the raw pointer
/// to non-confidential memory which is never dereferenced inside the security monitor. Its address is
/// used only to map a page located in the non-confidential memory to the address space of a confidential VM.
unsafe impl Send for SharedPage {}
unsafe impl Sync for SharedPage {}

impl SharedPage {
    pub fn new(
        hypervisor_address: NonConfidentialMemoryAddress, size: PageSize, confidential_vm_address: ConfidentialVmPhysicalAddress,
    ) -> Result<Self, Error> {
        // Security: check that the end address is located in the non-confidential memory
        MemoryLayout::read().non_confidential_address_at_offset(&hypervisor_address, size.in_bytes() - 1)?;

        Ok(Self { hypervisor_address, confidential_vm_address, size })
    }
}
