// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![rr::import("ace.theories.page_table", "page_table")]
use crate::core::architecture::mmu::page_table_entry::{LogicalPageTableEntry, PageTableEntry};
use crate::core::architecture::mmu::page_table_level::PageTableLevel;
use crate::core::architecture::mmu::paging_system::PagingSystem;
use crate::core::architecture::mmu::HgatpMode;
use crate::core::architecture::{PageSize, SharedPage};
use crate::core::control_data::MeasurementDigest;
use crate::core::memory_layout::{ConfidentialMemoryAddress, ConfidentialVmPhysicalAddress, NonConfidentialMemoryAddress};
use crate::core::page_allocator::{Allocated, Page, PageAllocator};
use crate::error::Error;
use alloc::boxed::Box;
use alloc::vec::Vec;
use sha2::digest::crypto_common::generic_array::GenericArray;

/// Represents an architectural 2nd level page table that defines the guest physical to real address translation. The security monitor fully
/// controls these mappings for confidential VMs. These page tables are stored in confidential memory (use `Page<Allocated>`).
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
///
/// Model: We model the page table by a `page_table_tree` which captures the inherent tree
/// structure.
#[rr::refined_by("pt_logical" : "page_table_tree")]
/// Invariant: We assert that there exists a serialized byte-level representation of the page table
/// tree in the form of a page.
#[rr::exists("pt_byte" : "page")]
#[rr::invariant("is_byte_level_representation pt_logical p_byte")]
pub struct PageTable {
    #[rr::field("pt_get_level pt_logical")]
    level: PageTableLevel,
    #[rr::field("pt_get_system pt_logical")]
    paging_system: PagingSystem,
    /// Serialized representation stores the architecture-specific, binary representation of the page table configuration that is read by
    /// the MMU.
    #[rr::field("pt_byte")]
    serialized_representation: Page<Allocated>,
    /// Logical representation stores a strongly typed page table configuration used by security monitor.
    #[rr::field("<#> (pt_get_entries pt_logical)")]
    logical_representation: Vec<LogicalPageTableEntry>,
}

/// Verification: what do we want to prove?
/// - the page table is structured according to RISC-V spec
/// - the page table has unique ownership over all "reachable" memory
/// - copying a page table from non-confidential memory only reads from non-confidential memory
/// - if input to copy_.. is not a valid page table, fail correctly
#[rr::skip]
impl PageTable {
    /// This functions copies recursively page table structure from non-confidential memory to confidential memory. It
    /// allocated a page in confidential memory for every page table. After this function executes, a valid page table
    /// configuration is in the confidential memory. Returns error if there is not enough memory to allocate this data structure.
    ///
    /// If the input page table configuration has two page table entries that point to the same page, then the copied page table
    /// configuration will have two page table entries pointing to different pages of the same content.
    ///
    /// # Safety
    ///
    /// This function expects a page table structure at the given `address` and will dereference
    /// this pointer and further pointers parsed from the page table structure, as long as they are
    /// in non-confidential memory.
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
    #[rr::params("l_nonconf", "ps", "level")]
    #[rr::args("l_nonconf", "ps", "level")]
    /// Precondition: We require the permission to copy from arbitrary non-confidential memory.
    /// Note that this implicitly specifies that we do not read from confidential memory.
    /// TODO: might need atomicity?
    #[rr::requires(#iris "permission_to_read_from_nonconfidential_mem")]
    // TODO: want to prove eventually
    //#[rr::ensures("value_has_security_level Hypervisor x")]
    // eventually: promote x from Hypervisor to confidential_vm_{new_id}
    #[rr::exists("x" : "result page_table_tree core_error_Error")]
    #[rr::returns("<#>@{result} x")]
    /* Alternative specification:
    // We won't need this for security, but if we were to trust the hypervisor, we could
    // prove this specification.
    //
    // SPEC 2:
    // For functional correctness (trusting the hypervisor):
    #[rr::params("l_nonconf", "ps", "level" : "nat", "pt" : "page_table_tree")]
    #[rr::args("l_nonconf", "ps", "level")]
    #[rr::requires(#iris "address_has_valid_page_table l_nonconf pt")]
    #[rr::exists("pt'")]
    #[rr::ensures("related_page_tables pt pt'")]
    #[rr::returns("#Ok(pt')")]   // (or out of memory)
    */
    pub fn copy_from_non_confidential_memory(
        address: NonConfidentialMemoryAddress, paging_system: PagingSystem, level: PageTableLevel,
    ) -> Result<Self, Error> {
        assert!(Page::<Allocated>::ENTRY_SIZE == paging_system.entry_size());

        let mut serialized_representation = PageAllocator::acquire_page(paging_system.memory_page_size(level))?
            .copy_from_non_confidential_memory(address)
            .map_err(|_| Error::AddressNotInNonConfidentialMemory())?;

        let logical_representation = serialized_representation
            .offsets()
            .map(|index| {
                // Below unwrap is ok because we iterate over valid offsets in the page, so `index` is valid.
                let serialized_entry = serialized_representation.read(index).unwrap();
                let logical_page_table_entry = match PageTableEntry::deserialize(serialized_entry) {
                    PageTableEntry::NotMapped => LogicalPageTableEntry::NotMapped,
                    PageTableEntry::PointerToNextPageTable(pointer) => {
                        let address = NonConfidentialMemoryAddress::new(pointer)?;
                        let lower_level = level.lower().ok_or(Error::PageTableCorrupted())?;
                        let page_table = Self::copy_from_non_confidential_memory(address, paging_system, lower_level)?;
                        LogicalPageTableEntry::PointerToNextPageTable(Box::new(page_table))
                    }
                    PageTableEntry::PointerToDataPage(pointer) => {
                        let address = NonConfidentialMemoryAddress::new(pointer)?;
                        let page_size = paging_system.data_page_size(level);
                        let page = PageAllocator::acquire_page(page_size)?.copy_from_non_confidential_memory(address)?;
                        LogicalPageTableEntry::PageWithConfidentialVmData(Box::new(page))
                    }
                };
                serialized_representation.write(index, logical_page_table_entry.serialize()).unwrap();
                Ok(logical_page_table_entry)
            })
            .collect::<Result<Vec<LogicalPageTableEntry>, Error>>()?;
        Ok(Self { level, paging_system, serialized_representation, logical_representation })
    }

    /// Creates an empty page table for the given page table level. Returns error if there is not enough memory to allocate this data
    /// structure.
    #[rr::params("system", "level")]
    #[rr::args("system", "level")]
    #[rr::exists("res")]
    #[rr::returns("<#>@{result} res")]
    #[rr::returns("if_Ok res (λ tree, tree = make_empty_page_tree system level)")]
    pub fn empty(paging_system: PagingSystem, level: PageTableLevel) -> Result<Self, Error> {
        let serialized_representation = PageAllocator::acquire_page(paging_system.memory_page_size(level))?.zeroize();
        let number_of_entries = serialized_representation.size().in_bytes() / paging_system.entry_size();
        let logical_representation = (0..number_of_entries).map(|_| LogicalPageTableEntry::NotMapped).collect();
        Ok(Self { level, paging_system, serialized_representation, logical_representation })
    }

    /// This function maps the given page shared with the hypervisor into the address space of the confidential VM. A previous mapping at
    /// the given guest physical address is overwritten. If the previous mapping pointed to a page in confidential memory, this page is
    /// deallocated and returned to the page allocator.
    ///
    /// This is a recursive function, which deepest execution is not larger than the number of paging system levels.
    ///
    /// # Confidential VM execution correctness
    ///
    /// The caller of this function must ensure that he synchronizes changes to page table configuration, i.e., by clearing address
    /// translation caches.
    pub fn map_shared_page(&mut self, shared_page: SharedPage) -> Result<(), Error> {
        let page_size_at_current_level = self.paging_system.data_page_size(self.level);
        ensure!(page_size_at_current_level >= shared_page.page_size(), Error::InvalidParameter())?;

        let virtual_page_number = self.paging_system.vpn(&shared_page.confidential_vm_address, self.level);
        if page_size_at_current_level > shared_page.page_size() {
            // We are at the intermediary page table. We will recursively go to the next page table, creating it in case it does not exist.
            match self.logical_representation.get_mut(virtual_page_number).ok_or_else(|| Error::PageTableConfiguration())? {
                LogicalPageTableEntry::PointerToNextPageTable(next_page_table) => next_page_table.map_shared_page(shared_page)?,
                LogicalPageTableEntry::NotMapped => {
                    let mut next_page_table = PageTable::empty(self.paging_system, self.level.lower().ok_or(Error::PageTableCorrupted())?)?;
                    next_page_table.map_shared_page(shared_page)?;
                    self.set_entry(virtual_page_number, LogicalPageTableEntry::PointerToNextPageTable(Box::new(next_page_table)));
                }
                _ => return Err(Error::PageTableConfiguration()),
            }
        } else {
            // We are at the correct page table level at which we must create the page table entry for the shared page. We will overwrite
            // whatever was there before. We end the recursion here.
            self.set_entry(virtual_page_number, LogicalPageTableEntry::PageSharedWithHypervisor(shared_page));
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
            LogicalPageTableEntry::PointerToNextPageTable(next_page_table) => next_page_table.unmap_shared_page(address),
            LogicalPageTableEntry::PageSharedWithHypervisor(shared_page) => {
                ensure!(&shared_page.confidential_vm_address == address, Error::PageTableConfiguration())?;
                self.set_entry(virtual_page_number, LogicalPageTableEntry::NotMapped);
                Ok(self.paging_system.data_page_size(self.level))
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
            LogicalPageTableEntry::PointerToNextPageTable(next_page_table) => next_page_table.translate(address),
            LogicalPageTableEntry::PageWithConfidentialVmData(page) => {
                let page_offset = self.paging_system.page_offset(address, self.level);
                // Below unsafe is ok because page_offset recorded in the page table entry is lower than the page size. Thus, we the
                // resulting address will still be in confidential memory because the page is in confidential memory by definition.
                Ok(unsafe { page.address().add(page_offset, page.end_address_ptr())? })
            }
            _ => Err(Error::AddressTranslationFailed()),
        }
    }

    /// Recursively extends measurements of all data pages in the order from the page with the lowest to the highest guest physical address.
    /// Returns error if the page table is malformed, i.e., there is a shared page mapping.
    pub fn measure(&self, digest: &mut MeasurementDigest, address: usize) -> Result<(), Error> {
        use sha2::Digest;
        self.logical_representation.iter().enumerate().try_for_each(|(i, entry)| {
            let guest_physical_address = address + i * self.paging_system.data_page_size(self.level).in_bytes();
            match entry {
                LogicalPageTableEntry::PointerToNextPageTable(next_page_table) => next_page_table.measure(digest, guest_physical_address),
                LogicalPageTableEntry::PageWithConfidentialVmData(page) => Ok(page.measure(digest, guest_physical_address)),
                LogicalPageTableEntry::PageSharedWithHypervisor(_) => Err(Error::PageTableConfiguration()),
                LogicalPageTableEntry::NotMapped => Ok(()),
            }
        })
    }

    /// Returns the physical address in confidential memory of the page table configuration.
    #[rr::params("pt")]
    #[rr::args("#pt")]
    #[rr::returns("pt_get_serialized_loc pt")]
    pub fn address(&self) -> usize {
        self.serialized_representation.start_address()
    }

    pub fn hgatp_mode(&self) -> HgatpMode {
        self.paging_system.hgatp_mode()
    }

    /// Set a new page table entry at the given index, replacing whatever was there before.
    #[rr::params("pt", "γ", "vpn", "pte")]
    #[rr::args("(#pt, γ)", "vpn", "pte")]
    /// Precondition: The vpn is valid for the number of entries of this page table.
    #[rr::requires("vpn < pt_number_of_entries pt")]
    /// Postcondition: The entry has been set correctly.
    #[rr::oberve("γ": "pt_set_entry pt vpn pte")]
    fn set_entry(&mut self, virtual_page_number: usize, entry: LogicalPageTableEntry) {
        self.serialized_representation.write(self.paging_system.entry_size() * virtual_page_number, entry.serialize()).unwrap();
        let entry_to_remove = core::mem::replace(&mut self.logical_representation[virtual_page_number], entry);
        if let LogicalPageTableEntry::PageWithConfidentialVmData(page) = entry_to_remove {
            PageAllocator::release_pages(alloc::vec![page.deallocate()]);
        }
    }

    /// Recursively clears the entire page table configuration, releasing all pages to the PageAllocator.
    #[rr::params("x")]
    #[rr::args("x")]
    pub fn deallocate(mut self) {
        let mut pages = Vec::with_capacity(self.logical_representation.len() + 1);
        pages.push(self.serialized_representation.deallocate());
        self.logical_representation.drain(..).for_each(|entry| match entry {
            LogicalPageTableEntry::PointerToNextPageTable(next_page_table) => next_page_table.deallocate(),
            LogicalPageTableEntry::PageWithConfidentialVmData(page) => pages.push(page.deallocate()),
            _ => {}
        });
        PageAllocator::release_pages(pages);
    }
}
