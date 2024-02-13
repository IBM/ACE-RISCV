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

/// A static global structure containing unallocated pages. Once<> guarantees that the PageAllocator can only be initialized once.
static PAGE_ALLOCATOR: Once<RwLock<PageAllocator>> = Once::new();

/// The `PageAllocator`'s job is to pass ownership of free pages residing in the confidential memory. It guarantees that a physical page is
/// not allocated twice. It does so by giving away `Page` tokens that represent ownership of a physical page located in the confidental
/// memory as described by `MemoryLayout`. `PageAllocator`'s constructor creates page tokens (maintaining an invariant that there are no two
/// page tokens describing the same physical address).
/// Specification:
/// We model the memory tracker by a finite map assigning page sizes to the number of available pages.
#[rr::refined_by("map" : "gmap page_size nat")]
/// Internally, the tracker stores a map with more information, containing the full model of the pages.
#[rr::exists("page_map : gmap page_size (Page_inv_t_rt)")]
/// This map is related by containing the number of pages as specified by `m`.
#[rr::invariants("page_allocator_maps_related map page_map")]
/// The internal map should have a vector of pages for every page size.
#[rr::invariants("∀ k : page_size, is_Some (page_map !! k)")]
pub struct PageAllocator {
    #[rr::field("page_map")]
    map: BTreeMap<PageSize, Vec<Page<UnAllocated>>>,
}

impl<'a> PageAllocator {
    // Usually there are 512 pages of size x that can fit in a single page of size y, where y is next page size larger than x (e.g., 2MiB
    // and 4KiB).
    const EXPECTED_NUMBER_OF_TOKENS_PER_SIZE: usize = 512;
    const NOT_INITIALIZED: &str = "Bug. Could not access page allocator because it is not initialized";

    /// Initializes the global instance of a `PageAllocator`. Returns error if the `PageAllocator` has already been initialized.
    ///
    /// # Arguments
    ///
    /// See the `PageAllocator::add_memory_region` for requirements on arguments.
    ///
    /// # Safety
    ///
    /// See the `PageAllocator::add_memory_region` for safety requirements.
    #[rr::skip]
    #[rr::params("start", "end", "vs")]
    #[rr::args("start", "end")]
    /// Precondition: The start address needs to be aligned to the minimum page size.
    #[rr::requires("Hstart_aligned" : "start `aligned_to` (page_size_in_bytes_nat Size4KiB)")]
    /// Precondition: The minimum page size divides the memory size.
    #[rr::requires("Hsz_div" : "(page_size_in_bytes_nat Size4KiB) | (end.2 - start.2)")]
    /// Precondition: The memory range should not be negative.
    #[rr::requires("Hstart_lt" : "start.2 ≤ end.2")]
    /// Precondition: We have ownership of the memory range, having (end - start) bytes.
    #[rr::requires(#type "start" : "vs" @ "array_t (int u8) (end.2 - start.2)")]
    /// Precondition: The page allocator should be uninitialized.
    #[rr::requires(#iris "once_status PAGE_ALLOCATOR None")]
    /// Postcondition: The page allocator is initialized.
    #[rr::ensures(#iris "once_status PAGE_ALLOCATOR (Some ())")]
    #[rr::returns("Ok(())")]
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
    #[rr::skip]
    #[rr::exists("m")]
    #[rr::returns("m")]
    fn empty() -> Self {
        let mut map = BTreeMap::new();
        for page_size in PageSize::all_from_largest_to_smallest() {
            let page_tokens = Vec::<_>::with_capacity(Self::EXPECTED_NUMBER_OF_TOKENS_PER_SIZE);
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
    #[rr::skip]
    // TODO: require the memory layout to be initialized
    #[rr::params("start", "end", "m", "γ")]
    #[rr::args("(#m, γ)", "start", "end")]
    /// Precondition: The start address needs to be aligned to the minimum page size.
    #[rr::requires("Hstart_aligned" : "start `aligned_to` (page_size_in_bytes_nat Size4KiB)")]
    /// Precondition: The minimum page size divides the memory size.
    #[rr::requires("Hsz_div" : "(page_size_in_bytes_nat Size4KiB) | (end.2 - start.2)")]
    /// Precondition: The memory range is positive.
    #[rr::requires("Hstart_lt" : "start.2 < end.2")]
    /// Precondition: We have ownership of the memory range, having (end - start) bytes.
    #[rr::requires(#type "start" : "vs" @ "array_t (int u8) (end.2 - start.2)")]
    /// Postcondition: There exists some correctly initialized page assignment.
    #[rr::exists("m'")]
    #[rr::observe("γ": "m'")]
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

    /// Returns page tokens that all together have ownership over a continous unallocated memory region of the requested size. Returns error
    /// if it could not obtain write access to the global instance of the page allocator or if there are not enough page tokens satisfying
    /// the requested criteria.
    #[rr::skip]
    #[rr::params("num", "sz")]
    #[rr::args("num", "sz")]
    /// Precondition: The page allocator needs to be initialized.
    #[rr::requires("once_status PAGE_ALLOCATOR (Some ())")]
    /// Postcondition: there exists a result (the error case is always a valid option)
    #[rr::exists("res")]
    /// Postcondition: errors are always a valid outcome
    #[rr::ensures("if_err res (λ err, err = error_Error_OutOfMemory)")]
    /// Postcondition: if sucessful, we get the desired number of pages of the right size
    #[rr::ensures("if_ok res (λ pages, length pages = num ∧ (∀ x, x ∈ pages → ∃ page, x = #page ∧ x.2 = sz))")]
    #[rr::returns("res")]
    pub fn acquire_continous_pages(number_of_pages: usize, page_size: PageSize) -> Result<Vec<Page<UnAllocated>>, Error> {
        let pages = Self::try_write(|page_allocator| Ok(page_allocator.acquire(number_of_pages, page_size)))?;
        assure_not!(pages.is_empty(), Error::OutOfPages())?;
        Ok(pages)
    }

    /// Consumes the page tokens given by the caller, allowing for their further acquisition. This is equivalent to deallocation of the
    /// physical memory region owned by the returned page tokens.
    ///
    /// TODO: to prevent fragmentation, run a procedure that will try to combine page tokens of smaller sizes into page tokens of bigger
    /// sizes. Otherwise, after long run, the security monitor's might start occupying to much memory (due to large number of page tokens)
    /// and being slow.
    #[rr::skip]
    #[rr::params("pages")]
    #[rr::args("pages")]
    /// Precondition: We require the page allocator to be initialized.
    #[rr::requires("once_status PAGE_ALLOCATOR (Some ())")]
    pub fn release_pages(pages: Vec<Page<UnAllocated>>) {
        let _ = Self::try_write(|page_allocator| {
            Ok(pages.into_iter().for_each(|page| {
                page_allocator.map.get_mut(&page.size()).and_then(|v| Some(v.push(page)));
            }))
        })
        .inspect_err(|_| debug!("Memory leak: failed to store released pages in the page allocator"));
    }

    #[rr::skip]
    #[rr::params("page")]
    #[rr::args("page")]
    /// Precondition: We require the page allocator to be initialized.
    #[rr::requires("once_status PAGE_ALLOCATOR (Some ())")]
    pub fn release_page(page: Page<UnAllocated>) {
        Self::release_pages(vec![page])
    }

    /// Returns vector of unallocated page tokens representing a continous memory region. If it failes to find allocation within free pages
    /// of the requested size, it divides larger page tokens. Empty vector is returned if there are not enough page tokens in the system
    /// that meet the requested criteria.
    // NOTE: this has the same specification as `acquire_continuous_pages_of_given_size`
    #[rr::skip]
    #[rr::params("m", "γ", "num", "sz")]
    #[rr::args("(#m, γ)", "num", "sz")]
    /// Precondition: We require the page allocator to be initialized.
    #[rr::requires("once_status PAGE_ALLOCATOR (Some ())")]
    #[rr::exists("pages", "m'")]
    /// Postcondition: If pages are available in the current PageAllocator, then we return them.
    #[rr::ensures("if decide (m !!! sz ≥ num) then length pages = num else length pages = 0")]
    /// Postcondition: The returned pages have the appropriate size
    #[rr::ensures("∀ p i, pages !! i = p → p.2 = sz")]
    /// Postcondition: The pages are continuous
    #[rr::ensures("pages_are_continuous pages")]
    /// Postcondition: The map has been updated.
    #[rr::observe("γ": "m'")]
    #[rr::returns("<#> pages")]
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
    #[rr::skip]
    #[rr::params("m", "γ", "num", "sz")]
    #[rr::args("(#m, γ)", "num", "sz")]
    /// Precondition: We require the page allocator to be initialized.
    #[rr::requires("once_status PAGE_ALLOCATOR (Some ())")]
    #[rr::exists("pages", "m'")]
    /// Postcondition: If pages are available in the current PageAllocator, then we return them.
    #[rr::ensures("if decide (m !!! sz ≥ num) then length pages = num else length pages = 0")]
    /// Postcondition: The returned pages have the appropriate size
    #[rr::ensures("∀ p i, pages !! i = p → p.2 = sz")]
    /// Postcondition: The pages are continuous
    #[rr::ensures("pages_are_continuous pages")]
    /// Postcondition: The map has been updated.
    #[rr::observe("γ": "m'")]
    #[rr::returns("<#> pages")]
    fn acquire_continous_pages_of_given_size(&mut self, number_of_pages: usize, page_size: PageSize) -> Vec<Page<UnAllocated>> {
        // Below unwrap is safe because the PageAllocator constructor guarantees that the map contains keys for every possible page size.
        let pages = self.map.get_mut(&page_size).unwrap();
        if pages.len() < number_of_pages {
            // early return because there is not enough page tokens for the requested page size.
            return vec![];
        }

        // Checks if consecutive pages at the given range compose a continuous memory region. The assumption is that pages are sorted.
        // Thus, it is enough to check if all neighbouring page tokens compose a continuous memory region.
        let is_memory_region_continous = |pages: &mut Vec<Page<UnAllocated>>, start_index: usize, end_index: usize| {
            (start_index..(end_index - 1)).all(|page_index| pages[page_index].end_address() == pages[page_index + 1].start_address())
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
    #[rr::skip]
    #[rr::params("m", "γ", "sz")]
    #[rr::args("(#m, γ)", "sz")]
    #[rr::exists("pages_available", "m'")]
    /// Postcondition: the page size division has been updated
    #[rr::observe("γ": "m'")]
    /// Postcondition: and there are sufficient pages at the requested size available
    #[rr::ensures("if pages_available then m' !!! sz ≥ 256 else True")]
    #[rr::returns("pages_available")]
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
    #[rr::skip]
    #[rr::params("m", "γ", "sz")]
    #[rr::args("(#m, γ)", "sz")]
    #[rr::exists("success", "m'")]
    /// Postcondition: the page size division has been updated
    #[rr::observe("γ": "m'")]
    /// Postcondition: if the division was successful, then sufficient pages at the requested size available
    #[rr::ensures("if success then m' !!! page_size_smaller sz ≥ 256 else m' = m")]
    #[rr::returns("success")]
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
    #[rr::skip]
    // TODO: might be challenging to specify
    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, PageAllocator>) -> Result<F, Error> {
        op(&mut PAGE_ALLOCATOR.get().expect(Self::NOT_INITIALIZED).write())
    }
}
