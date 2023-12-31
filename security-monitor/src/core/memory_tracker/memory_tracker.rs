// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use super::page::{Page, UnAllocated};
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout};
use crate::core::memory_protector::PageSize;
use crate::error::Error;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Range;
use spin::{Once, RwLock, RwLockWriteGuard};

const NOT_INITIALIZED_MEMORY_TRACKER: &str = "Bug. Could not access memory tracker because it is not initialized";

/// A static global structure containing unallocated pages. Once<> guarantees
/// that it the memory tracker can only be initialized once.
pub static MEMORY_TRACKER: Once<RwLock<MemoryTracker>> = Once::new();

/// Memory tracker allocates pages of confidential memory. It guarantees that a single page is not
/// allocated twice. It does so by giving away page tokens that represent ownership of a page in a
/// confidental memory. Page tokens are created when constructing the memory tracker.
pub struct MemoryTracker {
    map: BTreeMap<PageSize, Vec<Page<UnAllocated>>>,
}

impl<'a> MemoryTracker {
    /// Constructs the memory tracker over the memory region defined by start and end addresses.
    /// It creates page tokens of unallocated pages.
    ///
    /// # Arguments:
    ///
    /// `memory_start` address must be aligned to the smallest page size.
    /// `memory_end` does not belong to the memory region owned by the memory tracker. The total memory
    /// size of the memory tracker must be a multiply of the smallest page size.
    ///
    /// # Safety
    ///
    /// This function must only be called only once during the system lifecycle. The caller must guarantee
    /// that the memory tracker becomes the exclusive owner of the memory region described by the input
    /// arguments.
    pub unsafe fn new(memory_start: ConfidentialMemoryAddress, memory_end: *const usize) -> Result<Self, Error> {
        debug!("Memory tracker {:x}-{:x}", memory_start.as_usize(), memory_end as usize);
        assert!(memory_start.is_aligned_to(PageSize::smallest().in_bytes()));
        assert!(memory_start.offset_from(memory_end) as usize % PageSize::smallest().in_bytes() == 0);

        let mut map = BTreeMap::new();
        let memory_layout = MemoryLayout::read();
        let mut page_address = memory_start;
        for page_size in &[PageSize::Size1GiB, PageSize::Size2MiB, PageSize::Size4KiB] {
            let free_memory_in_bytes = usize::try_from(page_address.offset_from(memory_end))?;
            let number_of_new_pages = free_memory_in_bytes / page_size.in_bytes();
            let new_pages = (0..number_of_new_pages)
                .map(|i| {
                    let page_offset_in_bytes = i * page_size.in_bytes();
                    let address = memory_layout.confidential_address_at_offset_bounded(
                        &mut page_address,
                        page_offset_in_bytes,
                        memory_end,
                    )?;
                    // Safety: It is safe to create this page token here if:
                    // 1) this `MemoryTracker` constructor is guaranteed to be called only once
                    // during the system lifetime
                    // 2) all pages created here are guaranteed to be disjoined.
                    let new_page = Page::<UnAllocated>::init(address, page_size.clone());
                    Ok(new_page)
                })
                .collect::<Result<Vec<_>, Error>>()?;
            debug!("Created {} page tokens of size {:?}", new_pages.len(), page_size);
            let pages_size_in_bytes = new_pages.len() * page_size.in_bytes();
            map.insert(page_size.clone(), new_pages);

            match memory_layout.confidential_address_at_offset_bounded(
                &mut page_address,
                pages_size_in_bytes,
                memory_end,
            ) {
                Ok(ptr) => page_address = ptr,
                Err(_) => break,
            }
        }

        Ok(Self { map })
    }

    pub fn acquire_continous_pages(
        number_of_pages: usize, page_size: PageSize,
    ) -> Result<Vec<Page<UnAllocated>>, Error> {
        let pages = try_write(|tracker| Ok(tracker.acquire(number_of_pages, page_size)))?;
        assure_not!(pages.is_empty(), Error::OutOfMemory())?;
        Ok(pages)
    }

    pub fn release_pages(pages: Vec<Page<UnAllocated>>) {
        let _ = try_write(|tracker| {
            Ok(pages.into_iter().for_each(|page| {
                tracker.map.get_mut(&page.size()).and_then(|v| Some(v.push(page)));
            }))
        })
        .inspect_err(|_| debug!("Memory leak: failed to store released pages in the memory tracker"));
    }

    pub fn release_page(page: Page<UnAllocated>) {
        Self::release_pages(vec![page])
    }

    fn acquire(&mut self, number_of_pages: usize, page_size: PageSize) -> Vec<Page<UnAllocated>> {
        self.find_allocation(number_of_pages, page_size)
            .and_then(|range| self.map.get_mut(&page_size).and_then(|pages| Some(pages.drain(range).collect())))
            .unwrap_or(vec![])
    }

    // this function will divide larger pages when it failes to find allocation within free pages of the requested size.
    fn find_allocation(&mut self, number_of_pages: usize, page_size: PageSize) -> Option<Range<usize>> {
        if self.find_allocation_within_page_size(number_of_pages, page_size).is_none() {
            self.divide_pages(page_size);
        }
        self.find_allocation_within_page_size(number_of_pages, page_size)
    }

    fn divide_pages(&mut self, page_size: PageSize) -> bool {
        let mut result = false;
        let mut page_size_to_divide = page_size.larger();
        while let Some(fs) = page_size_to_divide {
            if fs == page_size {
                break;
            }
            if self.divide_page(fs) {
                page_size_to_divide = fs.smaller();
                result = true;
            } else {
                page_size_to_divide = fs.larger();
            }
        }
        result
    }

    /// Tries to divide a page of size 'from' into smaller pages
    fn divide_page(&mut self, from: PageSize) -> bool {
        if let Some(to) = from.smaller() {
            if let Some(page) = self.map.get_mut(&from).and_then(|pages| pages.pop()) {
                if let Some(ref mut pages) = self.map.get_mut(&to) {
                    pages.append(&mut page.divide());
                    return true;
                }
            }
        }
        false
    }

    fn find_allocation_within_page_size(
        &mut self, number_of_pages: usize, page_size: PageSize,
    ) -> Option<Range<usize>> {
        if let Some(pages) = self.map.get_mut(&page_size) {
            if pages.len() < number_of_pages {
                return None;
            }
            // check if there is a continous region of requested pages
            let are_pages_continous = |pages: &mut Vec<Page<UnAllocated>>, j: usize| {
                // should we do below calculation using pointers and its `byte_offset_from` method?
                pages[j].end_address() == pages[j + 1].start_address()
            };

            for i in 0..(pages.len() - number_of_pages) {
                for j in i..(i + number_of_pages) {
                    if !are_pages_continous(pages, j) {
                        // this is not a continous allocation
                        break;
                    }
                    if j == i + number_of_pages - 1 {
                        return Some(Range { start: i, end: i + number_of_pages });
                    }
                }
            }
        }
        None
    }
}

fn try_write<F, O>(op: O) -> Result<F, Error>
where O: FnOnce(&mut RwLockWriteGuard<'static, MemoryTracker>) -> Result<F, Error> {
    MEMORY_TRACKER
        .get()
        .expect(NOT_INITIALIZED_MEMORY_TRACKER)
        .try_write()
        .ok_or(Error::OptimisticLocking())
        .and_then(|ref mut memory_tracker| op(memory_tracker))
}
