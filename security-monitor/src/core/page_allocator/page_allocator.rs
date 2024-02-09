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
use spin::{Once, RwLock, RwLockWriteGuard};

const NOT_INITIALIZED_PAGE_ALLOCATOR: &str = "Bug. Could not access page allocator because it is not initialized";

/// A static global structure containing unallocated pages. Once<> guarantees that it the PageAllocator can only be initialized once.
static PAGE_ALLOCATOR: Once<RwLock<PageAllocator>> = Once::new();

/// The `PageAllocator`'s job is to pass ownership of free pages residing in the confidential memory. It guarantees that a physical page is not
/// allocated twice. It does so by giving away `Page` tokens that represent ownership of a physical page located in the confidental memory as described by `MemoryLayout`.
/// `PageAllocator`'s constructor creates page tokens (maintaining an invariant that there are no two page tokens describing the same physical
/// address).
pub struct PageAllocator {
    map: BTreeMap<PageSize, Vec<Page<UnAllocated>>>,
}

impl<'a> PageAllocator {
    /// Initializes the global instance of a `PageAllocator`. Returns error if it has already been initialized.
    ///
    /// # Arguments:
    ///
    /// See the `PageAllocator::new` for requirements on arguments.
    ///    
    /// # Safety
    ///
    /// See the `PageAllocator::new` for safety requirements.
    pub unsafe fn initialize(memory_start: ConfidentialMemoryAddress, memory_end: *const usize) -> Result<(), Error> {
        let page_allocator = unsafe { Self::new(memory_start, memory_end) }?;
        assure_not!(PAGE_ALLOCATOR.is_completed(), Error::Reinitialization())?;
        PAGE_ALLOCATOR.call_once(|| RwLock::new(page_allocator));
        Ok(())
    }

    /// Constructs the PageAllocator over the memory region defined by start and end addresses.
    /// It creates page tokens of unallocated pages.
    ///
    /// # Arguments:
    ///
    /// `memory_start` address must be aligned to the smallest page size.
    /// `memory_end` is one-past-the end of the memory region owned by the `PageAllocator`. The total memory
    /// size assigned to the `PageAllocator` must be a multiple of the smallest page size.
    ///
    /// # Guarantees
    ///
    /// * The map contains keys for every possible page size.
    /// * There are no two page tokens that describe the same memory address.
    ///
    /// # Safety
    ///
    /// This function must only be called once during the system lifecycle. The caller must guarantee
    /// that the PageAllocator becomes the exclusive owner of the memory region described by the input
    /// arguments.
    unsafe fn new(memory_start: ConfidentialMemoryAddress, memory_end: *const usize) -> Result<Self, Error> {
        debug!("Memory tracker {:x}-{:x}", memory_start.as_usize(), memory_end as usize);
        assert!(memory_start.is_aligned_to(PageSize::smallest().in_bytes()));
        assert!(memory_start.offset_from(memory_end) as usize % PageSize::smallest().in_bytes() == 0);

        let mut map = BTreeMap::new();
        let memory_layout = MemoryLayout::read();

        let mut next_address = Ok(memory_start);
        for page_size in PageSize::all_from_largest_to_smallest() {
            let page_tokens = match next_address {
                Ok(ref mut address) => {
                    let page_tokens = Self::create_page_tokens(address, memory_end, page_size)?;
                    let occupied_memory_in_bytes = page_tokens.len() * page_size.in_bytes();
                    next_address = memory_layout.confidential_address_at_offset_bounded(address, occupied_memory_in_bytes, memory_end);
                    page_tokens
                }
                Err(_) => Vec::<_>::with_capacity(512),
            };
            debug!("Created {} page tokens of size {:?}", page_tokens.len(), page_size);
            map.insert(page_size.clone(), page_tokens);
        }

        Ok(Self { map })
    }

    /// Creates page tokens of the given size over the given memory region.
    unsafe fn create_page_tokens(
        memory_start: &mut ConfidentialMemoryAddress, memory_end: *const usize, page_size: PageSize,
    ) -> Result<Vec<Page<UnAllocated>>, Error> {
        let memory_layout = MemoryLayout::read();
        let free_memory_in_bytes = usize::try_from(memory_start.offset_from(memory_end))?;
        let number_of_new_pages = free_memory_in_bytes / page_size.in_bytes();
        (0..number_of_new_pages)
            .map(|page_number| {
                let page_offset_in_bytes = page_number * page_size.in_bytes();
                let address = memory_layout.confidential_address_at_offset_bounded(memory_start, page_offset_in_bytes, memory_end)?;
                // Safety: It is safe to create this page token here if:
                // 1) this `MemoryTracker` constructor is guaranteed to be called only once
                // during the system lifetime
                // 2) all pages created here are guaranteed to be disjoint.
                Ok(Page::<UnAllocated>::init(address, page_size.clone()))
            })
            .collect::<Result<Vec<_>, Error>>()
    }

    /// Returns page tokens that all together have ownership over a continous unallocated memory region of the requested size. Returns error
    /// if it could not obtain write access to the global instance of the page allocator or if there are not enough page tokens satisfying the
    /// requested criteria.
    pub fn acquire_continous_pages(number_of_pages: usize, page_size: PageSize) -> Result<Vec<Page<UnAllocated>>, Error> {
        let pages = Self::try_write(|page_allocator| Ok(page_allocator.acquire(number_of_pages, page_size)))?;
        assure_not!(pages.is_empty(), Error::OutOfMemory())?;
        Ok(pages)
    }

    /// Consumes the page tokens given by the caller, allowing for their further acquisition. This is equivalent to deallocation of the
    /// physical memory region owned by the returned page tokens.
    ///
    /// TODO: to prevent fragmentation, run a procedure that will try to combine page tokens of smaller sizes into page tokens of bigger
    /// sizes. Otherwise, after long run, the security monitor's might start occupying to much memory (due to large number of page tokens)
    /// and being slow.
    pub fn release_pages(pages: Vec<Page<UnAllocated>>) {
        let _ = Self::try_write(|page_allocator| {
            Ok(pages.into_iter().for_each(|page| {
                page_allocator.map.get_mut(&page.size()).and_then(|v| Some(v.push(page)));
            }))
        })
        .inspect_err(|_| debug!("Memory leak: failed to store released pages in the page allocator"));
    }

    pub fn release_page(page: Page<UnAllocated>) {
        Self::release_pages(vec![page])
    }

    /// Returns vector of unallocated page tokens representing a continous memory region. If it failes to find allocation within free pages
    /// of the requested size, it divides larger page tokens. Empty vector is returned if there are not enough page tokens in the system that
    /// meet the requested criteria.
    fn acquire(&mut self, number_of_pages: usize, page_size: PageSize) -> Vec<Page<UnAllocated>> {
        let mut available_pages = self.acquire_continous_pages_of_given_size(number_of_pages, page_size);
        // it might be that there is not enough page tokens of the requested page size. In such a case, let's try to divide page tokens of
        // larger page sizes and try the allocation again.
        if available_pages.is_empty() {
            self.divide_pages(page_size);
            available_pages = self.acquire_continous_pages_of_given_size(number_of_pages, page_size);
        }
        available_pages
    }

    /// Tries to allocate a continous chunk of physical memory composed of the requested number of pages. Returns a vector of unallocated
    /// page tokens, all of them having the same size, or an empty vector if the allocation fails.
    fn acquire_continous_pages_of_given_size(&mut self, number_of_pages: usize, page_size: PageSize) -> Vec<Page<UnAllocated>> {
        // Below unwrap is safe because the PageAllocator constructor guarantees that the map contains keys for every possible page size.
        let pages = self.map.get_mut(&page_size).unwrap();
        if pages.len() < number_of_pages {
            // early return because there is not enough page tokens for the requested page size.
            return vec![];
        }

        // Checks if consecutive pages at the given range compose a continous memory region. The assumption is that pages are sorted.
        // Thus, it is enough to look check if all neighboring page tokens compose a continous memory region.
        let is_memory_region_continous = |pages: &mut Vec<Page<UnAllocated>>, start_index: usize, end_index: usize| {
            (start_index..(end_index - 1))
                .map(|page_index| pages[page_index].end_address() == pages[page_index + 1].start_address())
                .fold(true, |accumulator, value| accumulator && value)
        };

        let mut allocated_pages = Vec::with_capacity(number_of_pages);
        let last_possible_index = pages.len() - number_of_pages;
        (0..last_possible_index)
            .find(|&allocation_start_index| {
                let allocation_end_index = allocation_start_index + number_of_pages;
                is_memory_region_continous(pages, allocation_start_index, allocation_end_index)
            })
            .inspect(|allocation_start_index| {
                // we found allocation, lets return page tokens to the caller
                (0..number_of_pages).for_each(|_| {
                    // `Vec::push` appends to the end of the vector, so we preserve the order of pages. `Vec::remove` removes the page token
                    // at the given index and shifts left all other page tokens, so we preserve the order of pages in the map
                    allocated_pages.push(pages.remove(*allocation_start_index))
                })
            });
        allocated_pages
    }

    /// Tries to divide existing page tokens, so that the PageAllocator has page tokens of the requested page size.
    fn divide_pages(&mut self, page_size: PageSize) {
        let mut page_size_to_divide_next = page_size.larger();
        while let Some(page_size_to_divide_now) = page_size_to_divide_next {
            if page_size_to_divide_now == page_size {
                break;
            }
            if self.divide_page(page_size_to_divide_now) {
                // as soon as we manage to find and divide a larger page token, we start to to iterate back over smaller page sizes and
                // divide them into even smaller page tokens. Eventually, we end up with the requested page_size that will exit the while
                // loop.
                page_size_to_divide_next = page_size_to_divide_now.smaller();
            } else {
                // in the case when there are no more page tokens in the system, the page_size_to_divide becomes eventually None and
                // exits the while loop.
                page_size_to_divide_next = page_size_to_divide_now.larger();
            }
        }
    }

    /// Tries to divide a page of the given size into smaller pages. Returns false if there is no page of the given size or the given size
    /// is the smallest possible page size supported by the architecture.
    fn divide_page(&mut self, from_size: PageSize) -> bool {
        from_size
            .smaller()
            .and_then(|to_size| {
                // Below unwraps are safe because the PageAllocator constructor guarantees that the map contains keys for every possible
                // page size.
                self.map.get_mut(&from_size).unwrap().pop().and_then(|page| {
                    self.map.get_mut(&to_size).unwrap().append(&mut page.divide());
                    Some(true)
                })
            })
            .unwrap_or(false)
    }

    /// returns a mutable reference to the PageAllocator after obtaining a lock on the mutex
    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, PageAllocator>) -> Result<F, Error> {
        op(&mut PAGE_ALLOCATOR.get().expect(NOT_INITIALIZED_PAGE_ALLOCATOR).write())
    }
}
