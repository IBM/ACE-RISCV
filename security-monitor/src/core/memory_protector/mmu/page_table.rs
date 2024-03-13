// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::{ConfidentialMemoryAddress, ConfidentialVmPhysicalAddress, NonConfidentialMemoryAddress};
use crate::core::memory_protector::mmu::page_table_entry::{
    PageTableAddress, PageTableBits, PageTableConfiguration, PageTableEntry, PageTablePermission,
};
use crate::core::memory_protector::mmu::page_table_memory::PageTableMemory;
use crate::core::memory_protector::mmu::paging_system::{PageTableLevel, PagingSystem};
use crate::core::page_allocator::{PageAllocator, SharedPage};
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

    pub fn map_shared_page(&mut self, shared_page: SharedPage) -> Result<(), Error> {
        self.page_table.map_shared_page(self.paging_system, shared_page)
    }

    pub fn unmap_shared_page(&mut self, address: ConfidentialVmPhysicalAddress) -> Result<(), Error> {
        self.page_table.unmap_shared_page(self.paging_system, address)
    }

    pub fn translate(&self, address: ConfidentialVmPhysicalAddress) -> Result<&ConfidentialMemoryAddress, Error> {
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
    /// configuration is in the confidential memory.
    fn copy_from_non_confidential_memory(
        address: NonConfidentialMemoryAddress, paging_system: PagingSystem, level: PageTableLevel,
    ) -> Result<Self, Error> {
        let mut page_table_memory = PageTableMemory::copy_from_non_confidential_memory(address, paging_system, level)?;
        // TODO: make sure there are no cycles in the page table hierarchy, otherwise we might get
        // in an infinite loop.
        let entries = page_table_memory
            .indices()
            .map(|index| {
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
                    PageTableEntry::Leaf(Box::new(page), configuration, permission)
                } else {
                    let lower_level = level.lower().ok_or(Error::PageTableCorrupted())?;
                    let address = NonConfidentialMemoryAddress::new(PageTableAddress::decode(entry_raw))?;
                    let page_table = Self::copy_from_non_confidential_memory(address, paging_system, lower_level)?;
                    let configuration = PageTableConfiguration::decode(entry_raw);
                    PageTableEntry::Pointer(Box::new(page_table), configuration)
                };
                page_table_memory.set_entry(index, &page_table_entry);
                Ok(page_table_entry)
            })
            .collect::<Result<Vec<PageTableEntry>, Error>>()?;
        Ok(Self { level, page_table_memory, entries })
    }

    fn empty(paging_system: PagingSystem, level: PageTableLevel) -> Result<Self, Error> {
        let page_table_memory = PageTableMemory::empty(paging_system, level)?;
        let entries = Vec::with_capacity(page_table_memory.number_of_entries());
        Ok(Self { level, page_table_memory, entries })
    }

    /// This function maps the confidential VM's physical address into the address of the page allocated by the
    /// hypervisor. The second-level page table is modified. If there was already a mapping, the address of a previosuly
    /// mapped page is returned. The below function works only for shared pages of size 4KiB.
    fn map_shared_page(&mut self, paging_system: PagingSystem, shared_page: SharedPage) -> Result<(), Error> {
        // walk from the root page table until the leaf node recreating the intermediary page tables if necessary.
        let virtual_page_number = paging_system.vpn(shared_page.confidential_vm_virtual_address(), self.level);
        let entry = self.entries.get_mut(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())?;
        match entry {
            PageTableEntry::Pointer(next_page_table, _) => {
                next_page_table.map_shared_page(paging_system, shared_page)?;
            }
            PageTableEntry::Leaf(_page, _configuration, _permission) => {
                // The virtual address is already mapped to this physical address. Let's detach the old address and map
                // the requested address
                // TODO: deallocate the old page only if it is the same size a the requested shared page size.
                // if not, return an error because it might be that a huge page is already mapped and the 4KiB
                // shared page is supposed to be inside this huge page --- this is not allowed.
                let new_entry = PageTableEntry::Shared(
                    shared_page,
                    PageTableConfiguration::shared_page_configuration(),
                    PageTablePermission::shared_page_permission(),
                );
                self.set_entry(virtual_page_number, new_entry);
            }
            PageTableEntry::Shared(_address, _configuration, _permission) => {
                // confidential VM virtual address already mapped to a physical address in non-confidential memory.
                // Let's simply re-map to the new address.
                let new_entry = PageTableEntry::Shared(
                    shared_page,
                    PageTableConfiguration::shared_page_configuration(),
                    PageTablePermission::shared_page_permission(),
                );
                self.set_entry(virtual_page_number, new_entry);
            }
            PageTableEntry::NotValid => {
                if self.level == PageTableLevel::Level1 {
                    // enough to just set the mapping because there was no page mapped yet
                    let new_entry = PageTableEntry::Shared(
                        shared_page,
                        PageTableConfiguration::shared_page_configuration(),
                        PageTablePermission::shared_page_permission(),
                    );
                    self.set_entry(virtual_page_number, new_entry);
                } else {
                    // intermediary page table does not exist, let's create it
                    let mut next_page_table = PageTable::empty(paging_system, self.level)?;
                    next_page_table.map_shared_page(paging_system, shared_page)?;
                    let new_entry = PageTableEntry::Pointer(Box::new(next_page_table), PageTableConfiguration::empty());
                    self.set_entry(virtual_page_number, new_entry);
                }
            }
        }
        Ok(())
    }

    pub fn unmap_shared_page(&mut self, _paging_system: PagingSystem, _address: ConfidentialVmPhysicalAddress) -> Result<(), Error> {
        panic!("Unimplemented");
    }

    /// Translates the guest physical address to host physical address by doing a page walk. Error is returned if there exists no mapping
    /// for the requested guest physical address or the address translates to a shared page.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    pub fn translate(
        &self, paging_system: PagingSystem, address: ConfidentialVmPhysicalAddress,
    ) -> Result<&ConfidentialMemoryAddress, Error> {
        let virtual_page_number = paging_system.vpn(address, self.level);
        let entry = self.entries.get(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())?;
        match entry {
            PageTableEntry::Pointer(next_page_table, _) => next_page_table.translate(paging_system, address),
            PageTableEntry::Leaf(page, _configuration, _permission) => Ok(page.address()),
            _ => Err(Error::AddressTranslationFailed()),
        }
    }

    pub(super) fn address(&self) -> usize {
        self.page_table_memory.start_address()
    }

    fn set_entry(&mut self, index: usize, entry: PageTableEntry) {
        self.page_table_memory.set_entry(index, &entry);
        let entry_to_remove = core::mem::replace(&mut self.entries[index], entry);
        if let PageTableEntry::Leaf(page, _, _) = entry_to_remove {
            PageAllocator::release_page(page.deallocate());
        }
    }
}

impl Drop for PageTable {
    fn drop(&mut self) {
        // We must deallocate only a page owned by the Leaf entry because there are no other PageTableEntries but Leaf
        // that own a page.
        self.entries.drain(..).for_each(|entry| {
            if let PageTableEntry::Leaf(page, _, _) = entry {
                PageAllocator::release_page(page.deallocate());
            }
        });
    }
}
