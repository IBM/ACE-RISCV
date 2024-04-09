// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::{ConfidentialMemoryAddress, ConfidentialVmPhysicalAddress, NonConfidentialMemoryAddress};
use crate::core::memory_protector::mmu::page_table_entry::{
    PageTableAddress, PageTableBits, PageTableConfiguration, PageTableEntry, PageTablePermission,
};
use crate::core::memory_protector::mmu::page_table_level::PageTableLevel;
use crate::core::memory_protector::mmu::page_table_memory::PageTableMemory;
use crate::core::memory_protector::mmu::paging_system::PagingSystem;
use crate::core::memory_protector::{PageSize, SharedPage};
use crate::core::page_allocator::PageAllocator;
use crate::error::Error;
use alloc::boxed::Box;
use alloc::vec::Vec;

pub struct RootPageTable {
    paging_system: PagingSystem,
    page_table: PageTable,
}

impl RootPageTable {
    pub fn copy_from_non_confidential_memory(address: NonConfidentialMemoryAddress, paging_system: PagingSystem) -> Result<Self, Error> {
        let page_table = PageTable::copy_from_non_confidential_memory(address, paging_system, paging_system.levels())?;
        Ok(Self { paging_system, page_table })
    }

    pub fn map_shared_page(
        &mut self, hypervisor_address: NonConfidentialMemoryAddress, page_size: PageSize,
        confidential_vm_physical_address: ConfidentialVmPhysicalAddress,
    ) -> Result<(), Error> {
        self.page_table.map_shared_page(self.paging_system, hypervisor_address, page_size, confidential_vm_physical_address)
    }

    pub fn unmap_shared_page(&mut self, address: &ConfidentialVmPhysicalAddress) -> Result<PageSize, Error> {
        self.page_table.unmap_shared_page(self.paging_system, address)
    }

    pub fn translate(&self, address: &ConfidentialVmPhysicalAddress) -> Result<ConfidentialMemoryAddress, Error> {
        self.page_table.translate(self.paging_system, address)
    }

    pub fn address(&self) -> usize {
        self.page_table.address()
    }

    pub fn paging_system(&self) -> &PagingSystem {
        &self.paging_system
    }
}

pub(super) struct PageTable {
    level: PageTableLevel,
    page_table_memory: PageTableMemory,
    entries: Vec<PageTableEntry>,
}

impl PageTable {
    /// This functions copies recursively page table structure from non-confidential memory to confidential memory. It
    /// allocated a page in confidential memory for every page table. After this function executes, a valid page table
    /// configuration is in the confidential memory. Returns error if there is not enough memory to allocate this data structure.
    ///
    /// If the input page table configuration has two page table entries that point to the same page, then the copied page table
    /// configuration will have two page table entries pointing to different pages of the same content.
    ///
    /// # Guarantees
    ///
    /// The copied page table configuration:
    ///   * does not have cycles,
    ///   * all page tables are in confidential memory,
    ///   * all `leaf` page table entries point to unique data page in confidential memory,
    ///   * all `pointer` page table entries point to another page table belonging to the same page table configuration.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    fn copy_from_non_confidential_memory(
        address: NonConfidentialMemoryAddress, paging_system: PagingSystem, level: PageTableLevel,
    ) -> Result<Self, Error> {
        let mut page_table_memory = PageTableMemory::copy_from_non_confidential_memory(address, paging_system, level)?;
        let entries = page_table_memory
            .indices()
            .map(|index| {
                // below unwrap is ok because we iterate over indices of the page table memory, so `index` is valid.
                let entry_raw = page_table_memory.entry(index).unwrap();
                let page_table_entry = if !PageTableBits::is_valid(entry_raw) {
                    PageTableEntry::NotValid
                } else if PageTableBits::is_leaf(entry_raw) {
                    let address = NonConfidentialMemoryAddress::new(PageTableAddress::decode(entry_raw))?;
                    let page_size = paging_system.page_size(level);
                    let page = PageAllocator::acquire_continous_pages(1, page_size)?
                        .remove(0)
                        .copy_from_non_confidential_memory(address)
                        .map_err(|_| Error::PageTableCorrupted())?;
                    let configuration = PageTableConfiguration::decode(entry_raw);
                    let permission = PageTablePermission::decode(entry_raw);
                    PageTableEntry::PageWithConfidentialVmData(Box::new(page), configuration, permission)
                } else {
                    let lower_level = level.lower().ok_or(Error::PageTableCorrupted())?;
                    let address = NonConfidentialMemoryAddress::new(PageTableAddress::decode(entry_raw))?;
                    let page_table = Self::copy_from_non_confidential_memory(address, paging_system, lower_level)?;
                    let configuration = PageTableConfiguration::decode(entry_raw);
                    PageTableEntry::PointerToNextPageTable(Box::new(page_table), configuration)
                };
                page_table_memory.set_entry(index, &page_table_entry);
                Ok(page_table_entry)
            })
            .collect::<Result<Vec<PageTableEntry>, Error>>()?;
        Ok(Self { level, page_table_memory, entries })
    }

    /// Creates an empty page table for the given page table level. Returns error if there is not enough memory to allocate this data
    /// structure.
    fn empty(paging_system: PagingSystem, level: PageTableLevel) -> Result<Self, Error> {
        let page_table_memory = PageTableMemory::empty(paging_system, level)?;
        let entries = Vec::with_capacity(page_table_memory.number_of_entries());
        Ok(Self { level, page_table_memory, entries })
    }

    /// This function maps the confidential VM's physical address into the address of the page allocated by the
    /// hypervisor.
    ///
    /// # Guarantees
    ///
    /// Successful execution of this function results in:
    ///   * The mapping of guest physical address to a real physical address in non-confidential memory,
    ///   * The mapped shared page is inside the non-confidential memory,
    ///   * Any previous mapping at the given guest physical address is overwritten,
    ///   * If the previous mapping pointed to a page in confidential memory, this page is deallocated and returned to the page allocator.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    fn map_shared_page(
        &mut self, paging_system: PagingSystem, hypervisor_address: NonConfidentialMemoryAddress, page_size: PageSize,
        confidential_vm_physical_address: ConfidentialVmPhysicalAddress,
    ) -> Result<(), Error> {
        let page_size_at_current_level = paging_system.page_size(self.level);
        assure!(page_size_at_current_level >= page_size, Error::InvalidArgument())?;
        let virtual_page_number = paging_system.vpn(&confidential_vm_physical_address, self.level);

        if page_size_at_current_level > page_size {
            // We are at the intermediary page table. We will recursively go to the next page table, creating it in case it does not exist.
            match self.entries.get_mut(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())? {
                PageTableEntry::PointerToNextPageTable(next_page_table, _) => {
                    next_page_table.map_shared_page(paging_system, hypervisor_address, page_size, confidential_vm_physical_address)?;
                }
                PageTableEntry::NotValid => {
                    let mut next_page_table = PageTable::empty(paging_system, self.level)?;
                    next_page_table.map_shared_page(paging_system, hypervisor_address, page_size, confidential_vm_physical_address)?;
                    self.set_entry(
                        virtual_page_number,
                        PageTableEntry::PointerToNextPageTable(Box::new(next_page_table), PageTableConfiguration::empty()),
                    );
                }
                _ => {
                    // We do not support corner cases when the confidential VM requests the creation of a shared page within another
                    // page (shared or confidential) of larger size. We end the recursion returning error.
                    return Err(Error::PageTableConfiguration());
                }
            }
        } else {
            // We are at the correct page table level at which we must create the page table entry for the shared page. We will overwrite
            // whatever was there before. We end the recursion here.
            self.set_entry(
                virtual_page_number,
                PageTableEntry::PageSharedWithHypervisor(
                    SharedPage::new(hypervisor_address, page_size, confidential_vm_physical_address)?,
                    PageTableConfiguration::shared_page_configuration(),
                    PageTablePermission::shared_page_permission(),
                ),
            );
        }
        Ok(())
    }

    /// Removes a shared page from the address space of the confidential VM. Returns error if there is no shared page mapped at the given
    /// address. Returns the size of the unmapped shared page on succeess.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    fn unmap_shared_page(&mut self, paging_system: PagingSystem, address: &ConfidentialVmPhysicalAddress) -> Result<PageSize, Error> {
        let virtual_page_number = paging_system.vpn(address, self.level);
        match self.entries.get_mut(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())? {
            PageTableEntry::PointerToNextPageTable(next_page_table, _) => next_page_table.unmap_shared_page(paging_system, address),
            PageTableEntry::PageSharedWithHypervisor(existing_address, _configuration, _permission) => {
                assure!(&existing_address.confidential_vm_address == address, Error::PageTableConfiguration())?;
                self.set_entry(virtual_page_number, PageTableEntry::NotValid);
                Ok(paging_system.page_size(self.level))
            }
            _ => Err(Error::PageTableConfiguration()),
        }
    }

    /// Translates the guest physical address to host physical address by doing a page walk. Error is returned if there exists no mapping
    /// for the requested guest physical address or the address translates to a shared page.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    pub fn translate(
        &self, paging_system: PagingSystem, address: &ConfidentialVmPhysicalAddress,
    ) -> Result<ConfidentialMemoryAddress, Error> {
        let virtual_page_number = paging_system.vpn(address, self.level);
        match self.entries.get(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())? {
            PageTableEntry::PointerToNextPageTable(next_page_table, _) => next_page_table.translate(paging_system, address),
            PageTableEntry::PageWithConfidentialVmData(page, _configuration, _permission) => {
                let page_offset = paging_system.page_offset(address, self.level);
                // below unsafe is ok because page_offset recorded in the page table entry is lower than the page size. Thus, we the
                // resulting address will still be in confidential memory because the page is in confidential memory by definition.
                Ok(unsafe { page.address().add(page_offset, page.end_address_ptr())? })
            }
            _ => Err(Error::AddressTranslationFailed()),
        }
    }

    /// Returns the physical address in confidential memory of the page table configuration.
    pub(super) fn address(&self) -> usize {
        self.page_table_memory.start_address()
    }

    /// Set a new page table entry at the given index, replacing whatever there was before.
    fn set_entry(&mut self, index: usize, entry: PageTableEntry) {
        self.page_table_memory.set_entry(index, &entry);
        let entry_to_remove = core::mem::replace(&mut self.entries[index], entry);
        if let PageTableEntry::PageWithConfidentialVmData(page, _, _) = entry_to_remove {
            PageAllocator::release_page(page.deallocate());
        }
    }
}

impl Drop for PageTable {
    /// When page table is dropped, we go through all its entries and make sure that confidential pages are returned to the page allocator.
    /// Otherwise, we would have a memory leak.
    fn drop(&mut self) {
        self.entries.drain(..).for_each(|entry| {
            if let PageTableEntry::PageWithConfidentialVmData(page, _, _) = entry {
                PageAllocator::release_page(page.deallocate());
            }
        });
    }
}
