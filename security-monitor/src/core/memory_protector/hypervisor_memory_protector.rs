// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::{iopmp, mmu, pmp, tlb};
use crate::core::architecture::Hgatp;
use crate::core::memory_layout::MemoryLayout;
use crate::error::Error;

/// Exposes an interface to configure the hardware memory isolation component to set memory access protection preventing
/// the hypervisor from accessing memory it does not own.
pub struct HypervisorMemoryProtector {}

impl HypervisorMemoryProtector {
    pub fn create() -> Self {
        Self {}
    }

    /// Configures the memory protection mechanism on the hart which executes this function.  
    ///
    /// # Safety
    ///
    /// Caller must ensure that:
    ///   * the `MemoryLayout` has been initialized,
    ///   * this function is called by all harts during their initialization.
    pub unsafe fn setup() -> Result<(), Error> {
        // We use RISC-V PMP mechanism to define that the confidential memory region is not accessible.
        // We use RISC-V IOPMP mechanism to ensure that no IO devices can access confidential memory region.
        let (confidential_memory_start, confidential_memory_end) = MemoryLayout::read().confidential_memory_boundary();
        pmp::split_memory_into_confidential_and_non_confidential(confidential_memory_start, confidential_memory_end)?;
        iopmp::protect_confidential_memory_from_io_devices(confidential_memory_start, confidential_memory_end)?;

        // Enable memory isolation protection. TLB shutdown is not needed because every hart will run this code during its initialization
        // and below function will clear all cached TLBs.
        pmp::close_access_to_confidential_memory();

        Ok(())
    }

    /// Reconfigures hardware to enable memory accesses initiated from this physical hart to memory regions owned by the
    /// hypervisor and denies accesses to all other memory regions.
    ///
    /// # Safety
    ///
    /// Caller must guarantee that the security monitor will transition in the finite state machine to the
    /// `non-confidential flow` and eventually to the hypervisor code.
    pub unsafe fn enable(&self, hgatp: &Hgatp) {
        pmp::close_access_to_confidential_memory();
        mmu::enable_address_translation_and_protection(hgatp);
        tlb::clear_hart_tlbs();
    }
}
