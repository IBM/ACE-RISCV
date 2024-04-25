// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::HgatpMode;
use crate::core::memory_layout::{ConfidentialMemoryAddress, ConfidentialVmPhysicalAddress, NonConfidentialMemoryAddress};
use crate::core::memory_protector::mmu::page_table_entry::{
    PageTableAddress, PageTableBits, PageTableConfiguration, PageTableEntry, PageTablePermission,
};
use crate::core::memory_protector::mmu::page_table_level::PageTableLevel;
use crate::core::memory_protector::mmu::paging_system::PagingSystem;
use crate::core::memory_protector::{PageSize, SharedPage};
use crate::core::page_allocator::{Allocated, Page, PageAllocator};
use crate::error::Error;
use alloc::boxed::Box;
use alloc::vec::Vec;

/// Represents the architectural 2nd level page table that configures guest physical to real address translation. The security monitor fully controls these mappings for confidential VMs.
///
/// We represent page table in two ways, logical and serialized, and make sure both are always equivalent, i.e., changes to the logical
/// representation triggers changes to the serialized representation, so these two are always synced. Since the security monitor is
/// uninterruptible and access to page table configuration is synchronized for different security monitor threads, the changes are
/// considered atomic.
///
/// # Safety
///
/// During the execution of a confidential hart, MMU might traverse the serialized representation. Our changes to this representation must
/// be atomic, so that MMU always reads a valid configuration.
pub struct PageTable {
    level: PageTableLevel,
    paging_system: PagingSystem,
    /// Serialized representation stores the architecture-specific, binary representation of the page table configuration that is read by
    /// the MMU.
    serialized_representation: Page<Allocated>,
    /// Logical representation stores a strongly typed page table configuration used by security monitor.
    logical_representation: Vec<PageTableEntry>,
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
    pub fn copy_from_non_confidential_memory(
        address: NonConfidentialMemoryAddress, paging_system: PagingSystem, level: PageTableLevel,
    ) -> Result<Self, Error> {
        let mut serialized_representation = PageAllocator::acquire_page(paging_system.memory_page_size(level))?
            .copy_from_non_confidential_memory(address)
            .map_err(|_| Error::PageTableCorrupted())?;

        let logical_representation = (0..serialized_representation.size().in_bytes())
            .step_by(paging_system.entry_size())
            .map(|index| {
                // below unwrap is ok because we iterate over indices of the page table memory, so `index` is valid.
                let entry_raw = serialized_representation.read(index).unwrap();
                let page_table_entry = if !PageTableBits::is_valid(entry_raw) {
                    PageTableEntry::NotValid
                } else if PageTableBits::is_leaf(entry_raw) {
                    let address = NonConfidentialMemoryAddress::new(PageTableAddress::decode(entry_raw))?;
                    let page_size = paging_system.page_size(level);
                    let page = PageAllocator::acquire_page(page_size)?
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
                serialized_representation.write(index, page_table_entry.encode()).unwrap();
                Ok(page_table_entry)
            })
            .collect::<Result<Vec<PageTableEntry>, Error>>()?;
        Ok(Self { level, paging_system, serialized_representation, logical_representation })
    }

    /// Creates an empty page table for the given page table level. Returns error if there is not enough memory to allocate this data
    /// structure.
    pub fn empty(paging_system: PagingSystem, level: PageTableLevel) -> Result<Self, Error> {
        let serialized_representation = PageAllocator::acquire_page(paging_system.memory_page_size(level))?.zeroize();
        let number_of_entries = serialized_representation.size().in_bytes() / paging_system.entry_size();
        let logical_representation = Vec::with_capacity(number_of_entries);
        Ok(Self { level, paging_system, serialized_representation, logical_representation })
    }

    /// This function maps the confidential VM's physical address into the address of the page allocated by the hypervisor.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    ///
    /// # Guarantees
    ///
    /// Successful execution of this function results in:
    ///   * The mapping of guest physical address to a real physical address in non-confidential memory,
    ///   * The mapped shared page is inside the non-confidential memory,
    ///   * Any previous mapping at the given guest physical address is overwritten,
    ///   * If the previous mapping pointed to a page in confidential memory, this page is deallocated and returned to the page allocator.
    ///
    /// # Confidential VM execution correctness
    ///
    /// The caller of this function must ensure that he synchronizes changes to page table configuration, i.e., by clearing address
    /// translation caches.
    pub fn map_shared_page(
        &mut self, hypervisor_address: NonConfidentialMemoryAddress, page_size: PageSize,
        confidential_vm_physical_address: ConfidentialVmPhysicalAddress,
    ) -> Result<(), Error> {
        let page_size_at_current_level = self.paging_system.page_size(self.level);
        assure!(page_size_at_current_level >= page_size, Error::InvalidArgument())?;
        let virtual_page_number = self.paging_system.vpn(&confidential_vm_physical_address, self.level);

        if page_size_at_current_level > page_size {
            // We are at the intermediary page table. We will recursively go to the next page table, creating it in case it does not exist.
            match self.logical_representation.get_mut(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())? {
                PageTableEntry::PointerToNextPageTable(next_page_table, _) => {
                    next_page_table.map_shared_page(hypervisor_address, page_size, confidential_vm_physical_address)?;
                }
                PageTableEntry::NotValid => {
                    let mut next_page_table = Box::new(PageTable::empty(self.paging_system, self.level)?);
                    next_page_table.map_shared_page(hypervisor_address, page_size, confidential_vm_physical_address)?;
                    let new_page_table_entry = PageTableEntry::PointerToNextPageTable(next_page_table, PageTableConfiguration::empty());
                    self.set_entry(virtual_page_number, new_page_table_entry);
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
    ///
    /// # Confidential VM execution correctness
    ///
    /// The caller of this function must ensure that he synchronizes changes to page table configuration, i.e., by clearing address
    /// translation caches.
    pub fn unmap_shared_page(&mut self, address: &ConfidentialVmPhysicalAddress) -> Result<PageSize, Error> {
        let virtual_page_number = self.paging_system.vpn(address, self.level);
        match self.logical_representation.get_mut(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())? {
            PageTableEntry::PointerToNextPageTable(next_page_table, _) => next_page_table.unmap_shared_page(address),
            PageTableEntry::PageSharedWithHypervisor(existing_address, _configuration, _permission) => {
                assure!(&existing_address.confidential_vm_address == address, Error::PageTableConfiguration())?;
                self.set_entry(virtual_page_number, PageTableEntry::NotValid);
                Ok(self.paging_system.page_size(self.level))
            }
            _ => Err(Error::PageTableConfiguration()),
        }
    }

    /// Translates the guest physical address to host physical address by doing a page walk. Error is returned if there exists no mapping
    /// for the requested guest physical address or the address translates to a shared page.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    pub fn translate(&self, address: &ConfidentialVmPhysicalAddress) -> Result<ConfidentialMemoryAddress, Error> {
        let virtual_page_number = self.paging_system.vpn(address, self.level);
        match self.logical_representation.get(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())? {
            PageTableEntry::PointerToNextPageTable(next_page_table, _) => next_page_table.translate(address),
            PageTableEntry::PageWithConfidentialVmData(page, _configuration, _permission) => {
                let page_offset = self.paging_system.page_offset(address, self.level);
                // below unsafe is ok because page_offset recorded in the page table entry is lower than the page size. Thus, we the
                // resulting address will still be in confidential memory because the page is in confidential memory by definition.
                Ok(unsafe { page.address().add(page_offset, page.end_address_ptr())? })
            }
            _ => Err(Error::AddressTranslationFailed()),
        }
    }

    /// Returns the physical address in confidential memory of the page table configuration.
    pub fn address(&self) -> usize {
        self.serialized_representation.start_address()
    }

    pub fn hgatp_mode(&self) -> HgatpMode {
        self.paging_system.hgatp_mode()
    }

    /// Set a new page table entry at the given index, replacing whatever was there before.
    fn set_entry(&mut self, virtual_page_number: usize, entry: PageTableEntry) {
        self.serialized_representation.write(self.paging_system.entry_size() * virtual_page_number, entry.encode()).unwrap();
        let entry_to_remove = core::mem::replace(&mut self.logical_representation[virtual_page_number], entry);
        if let PageTableEntry::PageWithConfidentialVmData(page, _, _) = entry_to_remove {
            PageAllocator::release_pages(alloc::vec![page.deallocate()]);
        }
    }

    /// Recursively clears the entire page table configuration, releasing all pages to the PageAllocator.
    pub fn deallocate(mut self) {
        let mut pages = Vec::with_capacity(self.logical_representation.len() + 1);
        pages.push(self.serialized_representation.deallocate());
        self.logical_representation.drain(..).for_each(|entry| match entry {
            PageTableEntry::PointerToNextPageTable(next_page_table, _) => {
                next_page_table.deallocate();
            }
            PageTableEntry::PageWithConfidentialVmData(page, _configuration, _permission) => {
                pages.push(page.deallocate());
            }
            _ => {}
        });
        PageAllocator::release_pages(pages);
    }
}
