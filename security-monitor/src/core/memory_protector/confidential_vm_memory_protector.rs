// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::Hgatp;
use crate::core::control_data::ConfidentialVmId;
use crate::core::memory_layout::{ConfidentialMemoryAddress, ConfidentialVmPhysicalAddress, NonConfidentialMemoryAddress};
use crate::core::memory_protector::mmu::{PageTable, PageTableConfiguration, PageTableEntry, PageTablePermission};
use crate::core::memory_protector::{mmu, pmp, SharedPage};
use crate::error::Error;

/// Exposes an interface to configure the hardware memory isolation component in a way that
/// it protects accesses to the memory which the confidential VM does not own.
pub struct ConfidentialVmMemoryProtector {
    // Stores the page table configuration of the confidential VM.
    root_page_table: PageTable,
    // Stores the value of the hypervisor G-stage address translation protocol register.
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
    pub fn from_vm_state(hgatp: &Hgatp) -> Result<Self, Error> {
        let root_page_table = mmu::copy_mmu_configuration_from_non_confidential_memory(hgatp)?;
        Ok(Self { root_page_table, hgatp: 0 })
    }

    pub fn set_confidential_vm_id(&mut self, id: ConfidentialVmId) {
        assert!(self.hgatp == 0);
        let hgatp = Hgatp::new(self.root_page_table.address(), self.root_page_table.hgatp_mode(), id.usize());
        self.hgatp = hgatp.bits();
    }

    /// Modifies the configuration of the underlying hardware memory isolation component (e.g., MMU) in a way that a
    /// shared page is mapped into the address space of the confidential VM.
    ///
    /// # Guarantees
    ///
    /// Successful execution of this function results in the mapping of guest physical address to a real physical address in
    /// non-confidential memory. To guarantee confidential VM's correctness, the caller must ensure that he will perform `TLB shutdown` on
    /// all confidential harts, so that all confidential harts see the newly mapped shared page.
    pub fn map_shared_page(
        &mut self, hypervisor_address: NonConfidentialMemoryAddress, confidential_vm_physical_address: ConfidentialVmPhysicalAddress,
    ) -> Result<(), Error> {
        let page_table_entry = PageTableEntry::PageSharedWithHypervisor(
            SharedPage::new(hypervisor_address, confidential_vm_physical_address)?,
            PageTableConfiguration::shared_page_configuration(),
            PageTablePermission::read_write_permissions(),
        );
        self.root_page_table.map_page_table_entry(SharedPage::SIZE, &confidential_vm_physical_address, page_table_entry)
    }

    /// Modifies the configuration of the underlying hardware memory isolation component (e.g., MMU) in a way that a
    /// shared page is unmapped from the address space of the confidential VM.
    ///
    /// To guarantee confidential VM's correctness, the caller must ensure that he will perform `TLB shutdown` on all confidential harts, so
    /// that all confidential harts do not use the unmaped shared page.
    pub fn unmap_shared_page(&mut self, confidential_vm_physical_address: &ConfidentialVmPhysicalAddress) -> Result<(), Error> {
        self.root_page_table.map_page_table_entry(SharedPage::SIZE, confidential_vm_physical_address, PageTableEntry::NotValid)
    }

    /// Translates guest physical address into a real physical address in the confidential memory. Returns error if the guest physical
    /// address is not mapped into the real physical address, i.e., page table walk fails.
    pub fn translate_address(&self, address: &ConfidentialVmPhysicalAddress) -> Result<ConfidentialMemoryAddress, Error> {
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
        assert!(self.hgatp != 0);
        pmp::open_access_to_confidential_memory();
        mmu::enable_address_translation(self.hgatp);
        super::tlb::clear_hart_tlbs();
    }

    pub fn into_root_page_table(self) -> PageTable {
        self.root_page_table
    }
}
