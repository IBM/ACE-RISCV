// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{HartArchitecturalState, Hgatp};
use crate::core::control_data::ConfidentialVmId;
use crate::core::memory_layout::{ConfidentialMemoryAddress, ConfidentialVmPhysicalAddress};
use crate::core::memory_protector::mmu::RootPageTable;
use crate::core::memory_protector::{mmu, pmp};
use crate::core::page_allocator::SharedPage;
use crate::error::Error;

/// Exposes an interface to configure the hardware memory isolation component in a way that
/// it protects accesses to the memory which the ConfidentialVM does not own.
pub struct ConfidentialVmMemoryProtector {
    // stores the page table configuration of the ConfidentialVM.
    root_page_table: RootPageTable,
    // stores the value of the hypervisor G-stage address translation protocol register.
    hgatp: usize,
}

impl ConfidentialVmMemoryProtector {
    /// Constructs the memory protector of a confidential VM from the dumped state of a hart that was running a
    /// non-confidential VM at the time it requested to be converted in a confidential VM. This function copies the
    /// entire configuration of the underlying hardware memory isolation component into the confidential memory.
    ///
    /// Returns an error if:
    ///   * the size of the VM is larger than the size of the available confidential memory,
    ///   * the configuration of the memory isolation component (MMU) is invalid.
    pub fn from_vm_state(hart_state: &HartArchitecturalState) -> Result<Self, Error> {
        let hgatp = Hgatp::from(hart_state.hgatp);
        let root_page_table = mmu::copy_mmu_configuration_from_non_confidential_memory(hgatp)?;
        Ok(Self { root_page_table, hgatp: 0 })
    }

    pub fn set_confidential_vm_id(&mut self, id: ConfidentialVmId) {
        let hgatp = Hgatp::new(self.root_page_table.address(), self.root_page_table.paging_system().hgatp_mode(), id.usize());
        self.hgatp = hgatp.bits();
    }

    /// Modifies the configuration of the underlying hardware memory isolation component (e.g., MMU) in a way that a
    /// shared page is mapped into the address space of the confidential VM.
    pub fn map_shared_page(&mut self, shared_page: SharedPage) -> Result<(), Error> {
        self.root_page_table.map_shared_page(shared_page)?;
        super::tlb::tlb_shutdown();
        Ok(())
    }

    /// Modifies the configuration of the underlying hardware memory isolation component (e.g., MMU) in a way that a
    /// shared page is unmapped from the address space of the confidential VM.
    pub fn unmap_shared_page(&mut self, address: ConfidentialVmPhysicalAddress) -> Result<(), Error> {
        self.root_page_table.unmap_shared_page(address)?;
        super::tlb::tlb_shutdown();
        Ok(())
    }

    pub fn translate(&self, address: ConfidentialVmPhysicalAddress) -> Result<&ConfidentialMemoryAddress, Error> {
        self.root_page_table.translate(address)
    }

    /// Reconfigures hardware to enable access initiated from this physical hart to memory regions owned by the
    /// confidential VM and deny access to all other memory regions.
    ///
    /// # Safety
    ///
    /// Caller must guarantee that the security monitor will transition in the finite state machine to the `confidential
    /// flow` and that the hgatp argument contains the correct id and the root page table address of the confidential VM
    /// that will be executed next.
    pub unsafe fn enable(&self) {
        pmp::open_access_to_confidential_memory();
        mmu::enable_address_translation(self.hgatp);
        super::tlb::tlb_shutdown();
    }
}
