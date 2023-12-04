// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use super::PagingSystem;
use crate::core::memory_tracker::{Allocated, MemoryTracker, Page};
use crate::core::mmu::page_table_entry::PageTableEntry;
use crate::core::mmu::paging_system::PageTableLevel;
use crate::core::mmu::PageSize;
use crate::core::pmp::NonConfidentialMemoryAddress;
use crate::error::Error;
use alloc::vec::Vec;
use core::ops::Range;

/// Abstraction over the physical memory region of the page table giving an
/// interface to easily access raw page table entries organized accross Pages.
pub(super) struct PageTableMemory {
    pages: Vec<Page<Allocated>>,
    number_of_entries: usize,
    entry_size: usize,
}

impl PageTableMemory {
    const PAGE_SIZE: PageSize = PageSize::Size4KiB;

    pub(super) fn copy_from_non_confidential_memory(
        address: NonConfidentialMemoryAddress, paging_system: PagingSystem, level: PageTableLevel,
    ) -> Result<Self, Error> {
        let number_of_pages = paging_system.configuration_pages(level);
        let pages = MemoryTracker::acquire_continous_pages(number_of_pages, Self::PAGE_SIZE)?
            .into_iter()
            .enumerate()
            .map(|(i, page)| {
                let address = NonConfidentialMemoryAddress::new(address.usize() + i * page.size().in_bytes())?;
                page.copy_from_non_confidential_memory(address)
            })
            .collect::<Result<Vec<Page<Allocated>>, Error>>()?;
        let number_of_entries = paging_system.entries(level);
        let entry_size = paging_system.entry_size();
        Ok(Self { pages, number_of_entries, entry_size })
    }

    pub(super) fn empty(paging_system: PagingSystem, level: PageTableLevel) -> Result<Self, Error> {
        let number_of_pages = paging_system.configuration_pages(level);
        let pages = MemoryTracker::acquire_continous_pages(number_of_pages, Self::PAGE_SIZE)?
            .into_iter()
            .map(|f| f.zeroize())
            .collect();
        let number_of_entries = paging_system.entries(level);
        let entry_size = paging_system.entry_size();
        Ok(Self { pages, number_of_entries, entry_size })
    }

    pub(super) fn start_address(&self) -> usize {
        // Safety: indexing 0 is fine because a PageTableMemory has at least one page.
        self.pages[0].start_address()
    }

    pub(super) fn number_of_entries(&self) -> usize {
        self.number_of_entries
    }

    pub(super) fn indices(&self) -> Range<usize> {
        Range { start: 0, end: self.number_of_entries }
    }

    pub(super) fn entry(&self, index: usize) -> Option<usize> {
        self.resolve_index(index).and_then(|(page_id, index_in_page)| {
            let offset_in_page = self.entry_size * index_in_page;
            self.pages.get(page_id).and_then(|page| page.read(offset_in_page).ok())
        })
    }

    pub(super) fn set_entry(&mut self, index: usize, entry: &PageTableEntry) {
        // skip unnecessary write to the memory. Pages in the confidential memory
        // are guaranteed to be zeroed when allocated and a not valid entry is just 0
        let value = entry.encode();
        if value == 0 {
            return;
        }

        self.resolve_index(index).and_then(|(page_id, index_in_page)| {
            let offset_in_page = self.entry_size * index_in_page;
            self.pages.get_mut(page_id).and_then(|ref mut page| page.write(offset_in_page, value).ok())
        });
    }

    fn resolve_index(&self, index: usize) -> Option<(usize, usize)> {
        if index < self.number_of_entries {
            // we can do this calculations because 1) pages are continous 2) vector stores pages
            // in the correct order. Thus, we treat them as a continous array of memory.
            let entries_per_page = Self::PAGE_SIZE.in_bytes() / self.entry_size;
            let page_id = index / entries_per_page;
            let index_in_page = index % entries_per_page;
            Some((page_id, index_in_page))
        } else {
            None
        }
    }
}

impl Drop for PageTableMemory {
    fn drop(&mut self) {
        let deallocated_pages: Vec<_> = self.pages.drain(..).map(|p| p.deallocate()).collect();
        MemoryTracker::release_pages(deallocated_pages);
    }
}
