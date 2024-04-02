// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use super::page::{Page, UnAllocated};
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout};
use crate::core::memory_protector::PageSize;
use crate::error::Error;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;
use spin::{Once, RwLock, RwLockWriteGuard};

/// A static global structure containing unallocated pages. Once<> guarantees that the PageAllocator can only be initialized once.
static PAGE_ALLOCATOR: Once<RwLock<PageAllocator>> = Once::new();

/// The `PageAllocator`'s job is to pass ownership of free pages residing in the confidential memory. It guarantees that a physical page is
/// not allocated twice. It does so by giving away `Page` tokens that represent ownership of a physical page located in the confidental
/// memory as described by `MemoryLayout`. `PageAllocator`'s constructor creates page tokens (maintaining an invariant that there are no two
/// page tokens describing the same physical address).
pub struct PageAllocator {
    map: BTreeMap<PageSize, Vec<Page<UnAllocated>>>,
}

impl<'a> PageAllocator {
    const NOT_INITIALIZED: &'static str = "Bug. Could not access page allocator because it is not initialized";

    /// Initializes the global instance of a `PageAllocator`. Returns error if the `PageAllocator` has already been initialized.
    ///
    /// # Arguments
    ///
    /// See the `PageAllocator::add_memory_region` for requirements on arguments.
    ///    
    /// # Safety
    ///
    /// See the `PageAllocator::add_memory_region` for safety requirements.
    pub unsafe fn initialize(memory_start: ConfidentialMemoryAddress, memory_end: *const usize) -> Result<(), Error> {
        assure_not!(PAGE_ALLOCATOR.is_completed(), Error::Reinitialization())?;
        let mut page_allocator = Self::empty();
        page_allocator.add_memory_region(memory_start, memory_end);
        PAGE_ALLOCATOR.call_once(|| RwLock::new(page_allocator));
        Ok(())
    }

    /// Constructs an empty page allocator that contains no tokens.
    ///
    /// # Guarantees
    ///
    /// * The PageAllocator's map contains keys for every possible page size.
    fn empty() -> Self {
        let mut map = BTreeMap::new();
        for page_size in PageSize::all_from_largest_to_smallest() {
            let page_tokens = Vec::<_>::with_capacity(PageSize::TYPICAL_NUMBER_OF_PAGES_INSIDE_LARGER_PAGE);
            map.insert(page_size.clone(), page_tokens);
        }
        Self { map }
    }

    /// Adds a physial memory region to the PageAllocator. The ownership over this memory region is passed from the caller to the
    /// PageAllocator. This function constructs page tokens over this memory region and stores them in the PageAllocator.
    ///
    /// # Arguments
    ///
    /// `memory_region_start` address must be aligned to the smallest page size and lower than `memory_region_end`.
    /// `memory_region_end` address must be aligned to the smallest page size. This address is one-past-the end of the memory region whose
    /// ownership is given to the `PageAllocator`.
    ///
    /// # Guarantees
    ///
    /// * There are no two page tokens that describe the same memory address.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that he passes the ownership to the memory region described by the input arguments to the PageAllocator.
    unsafe fn add_memory_region(&mut self, memory_region_start: ConfidentialMemoryAddress, memory_region_end: *const usize) {
        debug!("Memory tracker: adding memory region: 0x{:x} - 0x{:x}", memory_region_start.as_usize(), memory_region_end as usize);
        assert!(memory_region_start.is_aligned_to(PageSize::smallest().in_bytes()));
        assert!(memory_region_end.is_aligned_to(PageSize::smallest().in_bytes()));
        assert!(memory_region_start.as_usize() < memory_region_end as usize);

        // Our strategy is to create as few page tokens as possible to keep the memory overhead as low as possible. Therefore, we prefer to
        // create page tokens for the largest page size when possible. We use a greedy approach. We look for the largest possible page that
        // can be accomodated for the given address and create a page token for it. We start with the smallest possible page size and then
        // keep increasing it until we find the largest possible page size. Then, we keep decreasing the page size until we reach the end of
        // the memory region.
        let memory_layout = MemoryLayout::read();
        let mut memory_address = Some(memory_region_start);
        let mut page_size = PageSize::smallest();

        // We might have to create a few tokens of 4KiB until we reach the address at which we can fit a 2MiB page. Then, we might have to
        // create a few tokens for 2MiB pages until we get the address where 1 GiB page would fit. Consider the following example,
        // where we first create 7x 4 KiB tokens (++), then 3x 2 MiB tokens (**), and only then start creating 1 GiB tokens (##).
        //
        //      ++ ++ ++ ++ ++ ++ ++  ***********************  ***********************  ***********************  ####
        // ||  |  |  |  |  |  |  |  ||  |  |  |  |  |  |  |  ||  |  |  |  |  |  |  |  ||  |  |  |  |  |  |  |  || ...
        //     ^memory_region_start  ^2 MiB                   ^2 MiB                   ^2 MiB                   ^1GiB
        //
        // At certain point we will not be able to fit more page tokens of the highest size (1GiB in our example) because remaining space
        // will be lower than the used page size. We might, however, still fit tokens of smaller sizes. This will be a analogous (but
        // opposite) situation to the one presented above. According to the following example, we will fit 3x 2 MiB (**) and 4x 4 KiB (++)
        // page tokens to the remaining memory region.
        //
        //   ***********************  ***********************  ***********************  ++ ++ ++ ++
        // ||  |  |  |  |  |  |  |  ||  |  |  |  |  |  |  |  ||  |  |  |  |  |  |  |  ||  |  |  |  |  |  |  |  || ...
        //  ^1 GiB                   ^2 MiB                   ^2 MiB                   ^2 MiB      ^memory_region_end

        // According to the RISC-V spec, pages must be aligned to their size.
        let is_address_page_aligned =
            |address: &ConfidentialMemoryAddress, page_size: &PageSize| address.is_aligned_to(page_size.in_bytes());
        // Page can be created only if all bytes are belonging to the given memory region
        let can_create_page = |address: &ConfidentialMemoryAddress, page_size: &PageSize| {
            let page_last_address = page_size.in_bytes() - 1;
            memory_layout.confidential_address_at_offset_bounded(&address, page_last_address, memory_region_end).is_ok()
        };

        while let Some(address) = memory_address.take() {
            // Let's find the largest possible size of a page that could align to this address.
            while let Some(larger_size) = page_size.larger().filter(|larger_size| is_address_page_aligned(&address, &larger_size)) {
                page_size = larger_size;
            }
            // Now let's find the largest size of a page that really fits in the given memory region. We do not have to check the alignment,
            // because the larger pages sizes are multiplies of the smaller page sizes.
            while let Some(smaller_size) = page_size.smaller().filter(|smaller_size| !can_create_page(&address, &smaller_size)) {
                page_size = smaller_size;
            }
            // The following line ensures that the while loop will complete because, regardless of whether we manage to create a page token
            // or not, we will increment the `memory_address` in each loop so that it eventually passes the end of the given memory region.
            memory_address = memory_layout.confidential_address_at_offset_bounded(&address, page_size.in_bytes(), memory_region_end).ok();
            // If the next memory address (`memory_address`) is still in the memory range, then we are sure we can create the page token.
            // Otherwise, we must check the boundary condition: Are we creating the last page token over a memory whose last byte
            // (`address`+`page_size.in_bytes()`) is next to the end of the memory region (`memory_region_end`)?
            if memory_address.is_some() || can_create_page(&address, &page_size) {
                let new_page_token = Page::<UnAllocated>::init(address, page_size.clone());
                // Below unwrap is safe because the PageAllocator constructor guarantees the initialization of the map for all possible page
                // sizes.
                self.map.get_mut(&page_size).unwrap().push(new_page_token);
            }
        }

        self.map.iter().for_each(|(page_size, tokens)| {
            debug!("Created {} page tokens of size {:?}", tokens.len(), page_size);
        })
    }

    /// Returns page tokens that all together have ownership over a continous unallocated memory region of the requested size and aligned to
    /// a specific page size. Returns error if it could not obtain write access to the global instance of the page allocator or if there are
    /// not enough page tokens satisfying the requested criteria.
    pub fn acquire_continous_pages(
        number_of_pages: usize, page_size: PageSize, align_to: PageSize,
    ) -> Result<Vec<Page<UnAllocated>>, Error> {
        let pages = Self::try_write(|page_allocator| Ok(page_allocator.acquire(number_of_pages, page_size, align_to)))?;
        assure_not!(pages.is_empty(), Error::OutOfPages())?;
        Ok(pages)
    }

    /// Returns a page token that has ownership over an unallocated memory region of the requested size.
    /// See `Self::acquire_continous_pages` for error conditions.
    pub fn acquire_page(page_size: PageSize) -> Result<Page<UnAllocated>, Error> {
        Self::acquire_continous_pages(1, page_size, page_size)?.pop().ok_or(Error::OutOfPages())
    }

    /// Consumes the page tokens given by the caller, allowing for their further acquisition. This is equivalent to deallocation of the
    /// physical memory region owned by the returned page tokens. Given vector of pages might contains pages of arbitrary sizes.
    pub fn release_pages(released_pages: Vec<Page<UnAllocated>>) {
        let number_of_released_pages = released_pages.len();
        if number_of_released_pages == 0 {
            return;
        }
        let mut map = BTreeMap::new();
        released_pages.into_iter().for_each(|page| {
            map.entry(*page.size()).or_insert_with(|| Vec::with_capacity(number_of_released_pages)).push(page);
        });
        let _ = Self::try_write(|page_allocator| {
            let mut modified_sizes = BTreeSet::new();
            map.into_iter().for_each(|(size, released_pages)| {
                modified_sizes.append(&mut page_allocator.insert_pages_of_the_same_size(released_pages, size));
            });
            page_allocator.defragment(modified_sizes);
            Ok(())
        })
        .inspect_err(|_| debug!("Memory leak: failed to store released pages in the page allocator"));
    }

    /// Combines contiguous pages into pages of a larger size, if possible.
    fn defragment(&mut self, mut modified_page_sizes: BTreeSet<PageSize>) {
        let mut page_size = PageSize::smallest();
        while let Some(larger_page_size) = page_size.larger() {
            if modified_page_sizes.contains(&page_size) {
                let number_of_pages = larger_page_size.in_bytes() / page_size.in_bytes();
                let mut larger_pages_to_insert = vec![];
                // Below unwrap is safe because the PageAllocator constructor guarantees that the map contains keys for every possible page
                // size.
                // Run defragmentation only if there is enough pages to possible merge them. For example, it make no sense to even try to
                // search for pages to merge, if we need at 512 pages and there is only 100. We also do not want to defragment to
                // agresively, because it might make sense to keep enough pages in the storage so that allocation is fast.
                while self.map.get(&page_size).unwrap().len() > 4 * number_of_pages {
                    let allocated_pages = self.acquire_continous_pages_of_given_size(number_of_pages, page_size, larger_page_size);
                    if allocated_pages.is_empty() {
                        break;
                    }
                    // Below invocation of unsafe is ok because (1) pages are ordered, (2) the first page is aligned to the larger page
                    // size, and (3) they all have the size of the larger page size.
                    let larger_page_to_insert = unsafe { Page::merge(allocated_pages, larger_page_size) };
                    larger_pages_to_insert.push(larger_page_to_insert)
                }
                modified_page_sizes.append(&mut self.insert_pages_of_the_same_size(larger_pages_to_insert, larger_page_size));
            }
            page_size = larger_page_size;
        }
    }

    /// Checks if consecutive pages at the given range compose a continuous memory region. The assumption is that pages are sorted.
    /// Thus, it is enough to check if all neighbouring page tokens compose a continuous memory region.
    fn are_pages_contigious(pages: &mut Vec<Page<UnAllocated>>, start_index: usize, number_of_pages: usize, page_size: PageSize) -> bool {
        if number_of_pages <= 1 {
            return true;
        }
        // Because pages are stored in the ascending order, it is enough to do boundary checking to reason if all pages are contiguous.
        let expected_end_address_of_last_page = pages[start_index].start_address() + number_of_pages * page_size.in_bytes();
        pages[start_index + number_of_pages - 1].end_address() == expected_end_address_of_last_page
    }

    /// Returns vector of unallocated page tokens representing a continous memory region. If it failes to find allocation within free pages
    /// of the requested size, it divides larger page tokens. Empty vector is returned if there are not enough page tokens in the system
    /// that meet the requested criteria.
    fn acquire(&mut self, number_of_pages: usize, page_size: PageSize, align_to: PageSize) -> Vec<Page<UnAllocated>> {
        let mut available_pages = self.acquire_continous_pages_of_given_size(number_of_pages, page_size, align_to);
        if available_pages.is_empty() {
            // It might be that there is not enough page tokens of the requested page size. In such a case, let's try to divide page tokens
            // of larger page sizes and try the allocation again.
            self.divide_pages(page_size);
            available_pages = self.acquire_continous_pages_of_given_size(number_of_pages, page_size, align_to);
        }
        available_pages
    }

    /// Tries to allocate a continous chunk of physical memory composed of the requested number of pages. Returns a vector of unallocated
    /// page tokens, all of them having the same size, or an empty vector if the allocation fails.
    fn acquire_continous_pages_of_given_size(
        &mut self, number_of_pages: usize, page_size: PageSize, align_to: PageSize,
    ) -> Vec<Page<UnAllocated>> {
        let mut acquired_pages = Vec::with_capacity(0);
        // Below unwrap is safe because the PageAllocator constructor guarantees that the map contains keys for every possible page size.
        let pages = self.map.get_mut(&page_size).unwrap();
        if number_of_pages == 0 || pages.len() < number_of_pages {
            return acquired_pages;
        }

        // Because we store pages in a `Vec`, the most performant way is to allocate from the end of the vector. Like this, we reduce the
        // number of elements shifts. Thus, we set index to the largest possible value at which we might find the first allocation.
        let mut index = pages.len() - number_of_pages;
        loop {
            // Improve performance by skipping pages that are not aligned. Since we did not find an allocation, let's calculate what is the
            // index of the next possible aligned address.
            let offset_from_next_aligned_address = if pages[index].address().is_aligned_to(align_to.in_bytes()) {
                if Self::are_pages_contigious(pages, index, number_of_pages, page_size) {
                    // We found allocation, lets return page tokens to the caller
                    acquired_pages = pages.drain(index..(index + number_of_pages)).collect();
                    break;
                }
                // We did not find the allocation. Let's check the next possible aligned address.
                align_to.in_bytes() / page_size.in_bytes()
            } else {
                // Since the current page is not correctly aligned, let's check at which offset a correctly aligned address might be. Since
                // we are iterating from the end to the beginning of addresses, we align down.
                let address_aligned_down = (pages[index].start_address() - 1) & !(align_to.in_bytes() - 1);
                (pages[index].start_address() - address_aligned_down) / page_size.in_bytes()
            };
            // Loop termination condition: the minimum index is 0
            if offset_from_next_aligned_address > index {
                break;
            }
            // Moving by the distance improves performence when searching for large allocation. This is heavily used during defragmentation
            // that searches for contiguous pages that can be combined into a larger page. For example, 2MiB page would contain 512 4KiB
            // pages. Thus, this allocation algorithm will eventually move the index by distance equal to 512.
            index -= offset_from_next_aligned_address;
        }
        acquired_pages
    }

    /// Inserts pages to the internal storage, while maintaining the sorted order. Returns a set that contains sizes of pages that might
    /// make sense to defragment.
    ///
    /// # Requirements
    ///
    /// Caller must guarantee that all given pages must be of the same size.
    fn insert_pages_of_the_same_size(&mut self, mut pages_to_insert: Vec<Page<UnAllocated>>, size: PageSize) -> BTreeSet<PageSize> {
        let mut modified_sizes = BTreeSet::new();
        if !pages_to_insert.is_empty() {
            // Below unwrap is safe because the PageAllocator constructor guarantees that the map contains keys for every possible page
            // size.
            let pages = self.map.get_mut(&size).unwrap();
            pages.append(&mut pages_to_insert);
            // We use `unstable` sort because there are no repeating elements in the vector (pages have unique addresses).
            pages.sort_unstable_by(|a, b| a.start_address().cmp(&b.start_address()));
            if pages.len() > 4 * PageSize::TYPICAL_NUMBER_OF_PAGES_INSIDE_LARGER_PAGE {
                modified_sizes.insert(size);
            }
        }
        modified_sizes
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
                    self.insert_pages_of_the_same_size(page.divide(), to_size);
                    Some(true)
                })
            })
            .unwrap_or(false)
    }

    /// returns a mutable reference to the PageAllocator after obtaining a lock on the mutex
    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, PageAllocator>) -> Result<F, Error> {
        op(&mut PAGE_ALLOCATOR.get().expect(Self::NOT_INITIALIZED).write())
    }
}
