// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![rr::include("option")]
#![rr::include("alloc")]
#![rr::include("btreemap")]
#![rr::include("vec")]
#![rr::include("spin")]
#![rr::import("ace.theories.page_allocator", "page_allocator")]
use super::page::{Page, UnAllocated};
use crate::core::architecture::PageSize;
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout};
use crate::error::Error;
use alloc::vec;
use alloc::vec::Vec;
use spin::{Once, RwLock, RwLockWriteGuard};

/// A static global structure containing unallocated pages. Once<> guarantees that the PageAllocator can only be initialized once.
//#[rr::name("PAGE_ALLOCATOR")]
static PAGE_ALLOCATOR: Once<RwLock<PageAllocator>> = Once::new();

/// This is a root node that represents the largest possible page size. Because of this implementation, there can be a maximum one page
/// token of the maximum size, and it will be then stored in the root node. It is reasonable as long as we do not support systems that have
/// more memory than 128TiB. For such systems, we must add larger page sizes.
/// Specification:
#[rr::refined_by("()" : "unit")]
#[rr::context("onceG Σ memory_layout")]
/// Invariant: We abstract over the root node
#[rr::exists("node" : "page_storage_node", "base_addr" : "Z", "node_size" : "page_size")]
/// Invariant: the allocator tree covers the first 128TiB of memory
#[rr::invariant("Hroot_base": "node.(base_address) = 0")]
/// Invariant: the page size is the largest
#[rr::invariant("Hroot_sz": "node.(max_node_size) = Size128TiB")]
#[rr::invariant("node_size = node.(max_node_size)")]
#[rr::invariant("base_addr = node.(base_address)")]
pub struct PageAllocator {
    #[rr::field("base_addr")]
    base_address: usize,
    #[rr::field("node_size")]
    page_size: PageSize,
    #[rr::field("node")]
    root: PageStorageTreeNode,
}

#[rr::context("onceG Σ memory_layout")]
#[rr::context("onceG Σ unit")]
impl PageAllocator {
    const NOT_INITIALIZED: &'static str = "Bug. Page allocator not initialized.";

    #[rr::only_spec]
    /// Initializes the global memory allocator with the given memory region as confidential memory. Must be called only once during the
    /// system initialization.
    ///
    /// # Arguments
    ///
    /// Both `memory_start` and `memory_end` must be aligned to 4KiB page boundaries.
    ///
    /// # Safety
    ///
    /// Caller must pass the ownership of the memory region [memory_start, memory_end).
    #[rr::params("vs", "MEMORY_CONFIG")]
    /// Precondition: The start and end addresses need to be aligned to the minimum page size.
    #[rr::requires("memory_start `aligned_to` (page_size_in_bytes_nat Size4KiB)")]
    #[rr::requires("memory_end `aligned_to` (page_size_in_bytes_nat Size4KiB)")]
    /// Precondition: The memory range is positive.
    #[rr::requires("memory_start.2 < memory_end.2")]

    /// Precondition: The memory range is within the region covered by the page allocator.
    #[rr::requires("memory_end.2 ≤ page_size_in_bytes_Z Size128TiB")]

    /// Precondition: We have ownership of the memory range, having (memory_end - memory_start) bytes.
    #[rr::requires(#type "memory_start" : "vs" @ "array_t (Z.to_nat (memory_end.2 - memory_start.2)) (int u8)")]

    /// Precondition: The memory needs to be in confidential memory
    #[rr::requires(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
    #[rr::requires("MEMORY_CONFIG.(conf_start).2 ≤ memory_start.2")]
    #[rr::requires("memory_end.2 ≤ MEMORY_CONFIG.(conf_end).2")]

    /// Precondition: The page allocator should be uninitialized.
    #[rr::requires(#iris "once_initialized π \"PAGE_ALLOCATOR\" None")]
    /// Postcondition: The page allocator is initialized.
    #[rr::ensures(#iris "once_initialized π \"PAGE_ALLOCATOR\" (Some ())")]
    #[rr::returns("Ok(())")]
    pub unsafe fn initialize(memory_start: ConfidentialMemoryAddress, memory_end: *const usize) -> Result<(), Error> {
        ensure_not!(PAGE_ALLOCATOR.is_completed(), Error::Reinitialization())?;
        let mut page_allocator = Self::empty();
        unsafe { page_allocator.add_memory_region(memory_start, memory_end)? };
        // NOTE: We initialize the invariant here.
        PAGE_ALLOCATOR.call_once(|| RwLock::new(page_allocator));
        Ok(())
    }

    /// Specification:
    /// Postcondition: an initialized memory allocator is returned
    #[rr::verify]
    fn empty() -> Self {
        Self { root: PageStorageTreeNode::empty(), base_address: 0, page_size: PageSize::largest() }
    }

    /// Find the largest page size we can create a page at.
    /// Precondition: The current address is aligned to the given page size.
    #[rr::requires("Haddr_aligned" : "address `aligned_to` page_size_in_bytes_nat page_size")]
    /// Precondition: The current address is in bounds of the given memory region.
    #[rr::requires("address.2 < memory_region_end.2")]
    /// Precondition: The current address and the bound are in bounds of the global memory layout.
    #[rr::requires("memory_layout.(conf_start).2 ≤ address.2")]
    #[rr::requires("memory_region_end.2 ≤ memory_layout.(conf_end).2")]
    /// Postcondition: The current address is aligned to the returned page size.
    #[rr::ensures("address `aligned_to` page_size_in_bytes_nat ret")]
    /// Postcondition: Either the returned page size is the smallest page size, or a page at the
    /// returned size will fit into the memory region.
    #[rr::ensures("ret = Size4KiB ∨ address.2 + page_size_in_bytes_nat ret ≤ memory_region_end.2")]
    fn find_largest_page_size(
        memory_layout: &MemoryLayout, mut page_size: PageSize, address: ConfidentialMemoryAddress, memory_region_end: *const usize,
    ) -> PageSize {
        // Let's find the largest possible size of a page that could align to this address.
        // According to the RISC-V spec, pages must be aligned to their size.
        while let Some(larger_size) = page_size.larger().filter(
            #[rr::returns("bool_decide ({address} `aligned_to` page_size_in_bytes_nat larger_size)")]
            |larger_size| address.is_aligned_to(larger_size.in_bytes()),
        ) {
            #[rr::inv_vars("page_size")]
            #[rr::inv("address `aligned_to` page_size_in_bytes_nat page_size")]
            #[rr::ignore]
            #[allow(unused)]
            || {};
            page_size = larger_size;
        }
        // After the loop, we have the largest possible `page_size` for which the `address` is
        // well-aligned.

        // Now let's find the largest size of a page that really fits in the given memory region. We do not have to check the alignment,
        // because the larger pages sizes are multiples of the smaller page sizes.
        while memory_layout.confidential_address_at_offset_bounded(&address, page_size.in_bytes() - 1, memory_region_end).is_err()
            && let Some(smaller_size) = page_size.smaller()
        {
            #[rr::inv_vars("page_size")]
            #[rr::inv("address `aligned_to` page_size_in_bytes_nat page_size")]
            #[rr::ignore]
            #[allow(unused)]
            || {};
            page_size = smaller_size;
        }
        // After the loop, we know that either no smaller page size exists, or a page at `page_size` fits in the memory region.

        page_size
    }

    #[rr::params("vs", "MEMORY_CONFIG")]
    /// Precondition: The start and end addresses need to be aligned to the minimum page size.
    #[rr::requires("Hstart_aligned" : "memory_region_start `aligned_to` (page_size_in_bytes_nat Size4KiB)")]
    #[rr::requires("Hend_aligned" : "memory_region_end `aligned_to` (page_size_in_bytes_nat Size4KiB)")]
    /// Precondition: The memory range is positive.
    #[rr::requires("Hstart_lt" : "memory_region_start.2 < memory_region_end.2")]

    /// Precondition: We have ownership of the memory range, having (mend - mstart) bytes.
    #[rr::requires(#type "memory_region_start" : "<#> vs" @ "array_t (Z.to_nat (memory_region_end.2 - memory_region_start.2)) (int u8)")]

    /// Precondition: The memory layout needs to be initialized
    #[rr::requires(#iris "once_initialized π \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
    /// Precondition: the whole memory region should be part of confidential memory
    #[rr::requires("MEMORY_CONFIG.(conf_start).2 ≤ memory_region_start.2")]
    #[rr::requires("memory_region_end.2 ≤ MEMORY_CONFIG.(conf_end).2")]

    #[rr::observe("self.ghost": "()")]

    #[rr::ok]
    /// Precondition: The memory range is within the region covered by the memory allocator.
    #[rr::requires("memory_region_end.2 ≤ page_size_in_bytes_Z Size128TiB")]
    #[rr::ensures("ret = tt")]
    unsafe fn add_memory_region(
        &mut self, memory_region_start: ConfidentialMemoryAddress, memory_region_end: *const usize,
    ) -> Result<(), Error> {
        //debug!("Memory tracker: adding memory region: 0x{:x} - 0x{:x}", memory_region_start.as_usize(), memory_region_end as usize);
        assert!(memory_region_start.is_aligned_to(PageSize::smallest().in_bytes()));
        assert!(memory_region_end.is_aligned_to(PageSize::smallest().in_bytes()));
        assert!(memory_region_start.as_usize() < memory_region_end as usize);
        // The page allocator can only handle memory regions up to the largest page size.
        ensure_not!(memory_region_end as usize > self.page_size.in_bytes(), Error::TooMuchMemory())?;

        // Our strategy is to create as few page tokens as possible to keep the memory overhead as low as possible. Therefore, we prefer to
        // create page tokens for the largest page size when possible. We use a greedy approach. We look for the largest possible page that
        // can be accomodated for the given address and create a page token for it. We start with the smallest possible page size and then
        // keep increasing it until we find the largest possible page size. Then, we keep decreasing the page size until we reach the end of
        // the memory region.
        let memory_layout = MemoryLayout::read();
        let mut address = memory_region_start;
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

        let node = &mut self.root;
        loop {
            #[rr::params("γ")]
            #[rr::inv_vars("page_size", "address", "node")]
            #[rr::inv("address `aligned_to` page_size_in_bytes_nat page_size")]
            #[rr::inv("memory_region_start.2 ≤ address.2")]
            #[rr::inv("address.2 < memory_region_end.2")]
            // Invariant: the borrow variable stays the same, but we do not track the state of the node
            #[rr::inv("γ = node.ghost")]
            // Invariant: the base address and node size stay unchanged
            #[rr::inv("node.cur.(base_address) = 0")]
            #[rr::inv("node.cur.(max_node_size) = Size128TiB")]
            // Invariant: Remaining memory ownership
            #[rr::exists("vs")]
            #[rr::inv(#type "address" : "<#> vs" @ "array_t (Z.to_nat (memory_region_end.2 - address.2)) (int u8)")]
            #[rr::ignore]
            #[allow(unused)]
            || {};

            // get the largest well-aligned address that fits into the memory region
            page_size = Self::find_largest_page_size(memory_layout, page_size, address, memory_region_end);

            // Check that we can actually create the page
            if memory_layout.confidential_address_at_offset_bounded(&address, page_size.in_bytes() - 1, memory_region_end).is_ok() {
                let new_page_token = unsafe { Page::<UnAllocated>::init(address, page_size) };
                // NOTE: We show that the page token is within the range of the allocator
                node.store_page_token(self.base_address, self.page_size, new_page_token);
            }

            // The following line ensures that the while loop will progress because, regardless of whether we manage to create a page token
            // or not, we will increment the `memory_address` in each loop so that it eventually passes the end of the given memory region.
            let Ok(new_addr) = memory_layout.confidential_address_at_offset_bounded(&address, page_size.in_bytes(), memory_region_end)
            else {
                // we passed beyond the memory region
                break;
            };
            address = new_addr;
        }
        Ok(())
    }

    #[rr::only_spec]
    /// Returns a page token that has ownership over an unallocated memory region of the requested size. Returns error if it could not
    /// obtain write access to the global instance of the page allocator or if there are not enough page tokens satisfying the requested
    /// criteria.
    /// Precondition: We require the page allocator to be initialized.
    #[rr::requires(#iris "once_initialized π \"PAGE_ALLOCATOR\" (Some ())")]
    /// Postcondition: If a page is returned, it has the right size.
    #[rr::ok]
    #[rr::ensures("ret.(page_sz) = page_size_to_allocate")]
    pub fn acquire_page(page_size_to_allocate: PageSize) -> Result<Page<UnAllocated>, Error> {
        Self::try_write(|page_allocator| {
            let base_address = page_allocator.base_address;
            let page_size = page_allocator.page_size;
            Ok(page_allocator.root.acquire_page_token(base_address, page_size, page_size_to_allocate))
        })?
    }

    #[rr::only_spec]
    /// Consumes the page tokens given by the caller, allowing for their further acquisition. This is equivalent to deallocation of the
    /// physical memory region owned by the returned page tokens. Given vector of pages might contains pages of arbitrary sizes.
    /// Precondition: We require the page allocator to be initialized.
    #[rr::requires(#iris "once_initialized π \"PAGE_ALLOCATOR\" (Some ())")]
    pub fn release_pages(released_pages: Vec<Page<UnAllocated>>) {
        let _ = Self::try_write(|page_allocator| {
            let base_address = page_allocator.base_address;
            let page_size = page_allocator.page_size;
            let root_node = &mut page_allocator.root;
            for page_token in released_pages {
                #[rr::params("γ")]
                #[rr::inv_vars("root_node", "page_size", "base_address")]
                #[rr::inv("base_address = 0%Z")]
                #[rr::inv("page_size = Size128TiB")]
                #[rr::inv("root_node.ghost = γ")]
                #[rr::ignore]
                #[allow(unused)]
                || {};
                // NOTE: we show that the token is within range of the allocator, using the
                // invariant of the page token.
                root_node.store_page_token(base_address, page_size, page_token);
            }
            Ok(())
        })
        .inspect_err(|_| debug!("Memory leak: failed to store released pages in the page allocator"));
    }

    #[rr::skip]
    /// returns a mutable reference to the PageAllocator after obtaining a lock on the mutex
    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, PageAllocator>) -> Result<F, Error> {
        op(&mut PAGE_ALLOCATOR.get().expect(Self::NOT_INITIALIZED).write())
    }
}

/// A node of a tree data structure that stores page tokens and maintains additional metadata that simplifies acquisition and
/// release of page tokens.
/// Specification:
#[rr::context("onceG Σ memory_layout")]
#[rr::refined_by("node" : "page_storage_node")]
/// We abstract over the components stored here
#[rr::exists("max_sz" : "option page_size")]
#[rr::exists("maybe_page_token" : "option page")]
#[rr::exists("children" : "list page_storage_node")]
/// Invariant: The representation invariant linking all these things together holds.
#[rr::invariant("page_storage_node_invariant node max_sz maybe_page_token children")]
/// Invariant: The whole address space of this node is in addressable memory.
#[rr::invariant("INV_IN_RANGE": "node.(base_address) + (page_size_in_bytes_nat node.(max_node_size)) ≤ MaxInt usize")]
struct PageStorageTreeNode {
    // Page token owned by this node. `None` means that this page token has already been allocated or that it has been divided into smaller
    // pages token that were stored in this node's children.
    #[rr::field("<#>@{{ option }} maybe_page_token")]
    page_token: Option<Page<UnAllocated>>,
    // Specifies what size of the page token can be allocated by exploring the tree starting at this node.
    // Invariant: if page token exist, then the its size is the max allocable size. Otherwise, the max allocable page size is the max
    // allocable page size of children
    #[rr::field("<#>@{{ option }} max_sz")]
    max_allocable_page_size: Option<PageSize>,
    // Invariant: Children store page tokens smaller than the page token stored in the parent node
    #[rr::field("<#> children")]
    children: Vec<Self>,
}

#[rr::context("onceG Σ memory_layout")]
impl PageStorageTreeNode {
    /// Creates a new empty node with no allocation.
    /// Specification:
    /// We can choose an arbitrary node size and base address.
    #[rr::params("node_size", "base_address")]
    /// Precondition: the base address needs to be suitably aligned.
    #[rr::requires("(page_size_align node_size | base_address)%Z")]
    /// Precondition: the whole memory range is in addressable memory.
    #[rr::requires("base_address + (page_size_in_bytes_nat node_size) ≤ MaxInt usize")]
    /// Postcondition: we get a node with no available pages.
    #[rr::returns("mk_page_node node_size base_address PageTokenUnavailable false")]
    fn empty() -> Self {
        Self { page_token: None, max_allocable_page_size: None, children: vec![] }
    }

    /// Recursively traverses the tree until it reaches the node that can store the given page token. Returns the largest size of a page
    /// token that can be allocated from this node. This method has the max depth of recusrive invocation equal to the number of
    /// PageSize variants. This method has an upper bounded computation complexity.
    ///
    /// Precondition: The size and base address arguments match the logical state.
    #[rr::requires("this_node_base_address = self.cur.(base_address)")]
    #[rr::requires("this_node_page_size = self.cur.(max_node_size)")]
    /// Precondition: The token we store has a smaller-or-equal size than the node.
    #[rr::requires("Hsz_le" : "page_token.(page_sz) ≤ₚ self.cur.(max_node_size)")]
    /// Precondition: The page token is within the range of the node.
    #[rr::requires("Hrange" : "page_within_range this_node_base_address this_node_page_size page_token")]
    /// Postcondition: The now available size is at least the size that we stored.
    #[rr::ensures("page_token.(page_sz) ≤ₚ ret")]
    /// Postcondition: This node has been changed...
    #[rr::exists("node'")]
    #[rr::observe("self.ghost": "node'")]
    /// ...and now it can allocate a page of the size given by the return value
    #[rr::ensures("page_node_can_allocate node' = Some ret")]
    /// ...which is at least the size of the token that was stored
    #[rr::ensures("page_token.(page_sz) ≤ₚ ret")]
    /// ...and which is at least as large as the size we could allocate before
    #[rr::ensures("page_node_can_allocate self.cur ≤o{ option_cmp page_size_cmp} Some ret")]
    /// ...and which is bounded by the node's size (this is an artifact of the proof)
    #[rr::ensures("ret ≤ₚ self.cur.(max_node_size)")]
    /// ...while the rest is unchanged
    #[rr::ensures("node'.(max_node_size) = self.cur.(max_node_size)")]
    #[rr::ensures("node'.(base_address) = self.cur.(base_address)")]
    fn store_page_token(
        &mut self, this_node_base_address: usize, this_node_page_size: PageSize, page_token: Page<UnAllocated>,
    ) -> PageSize {
        assert!(this_node_page_size >= page_token.size());
        if this_node_page_size == page_token.size() {
            // End of recursion, we found the node that can store the page token.
            assert!(this_node_base_address == page_token.start_address());
            assert!(this_node_page_size == page_token.size());
            // For verification: to unfold invariant.
            &self.max_allocable_page_size;

            self.store_page_token_in_this_node(page_token);
        } else {
            assert!(this_node_page_size.smaller().is_some());
            self.initialize_children_if_needed(this_node_page_size);

            // Calculate which child should we invoke recursively.
            let index = Self::calculate_child_index(this_node_base_address, this_node_page_size, &page_token);
            // Let's go recursively to the node where this page belongs to.
            let (child_base_address, child_page_size) = self.child_address_and_size(this_node_base_address, this_node_page_size, index);
            let allocable_page_size =
                vec_index_mut(&mut self.children, index).store_page_token(child_base_address, child_page_size, page_token);
            // We are coming back from the recursion.
            // Update the size, in case the recursion increased the allocable size.
            self.max_allocable_page_size = self.max_allocable_page_size.max(Some(allocable_page_size));
            // In case this token became mergeable, merge.
            // Safety: The children are initialized.
            unsafe {
                self.try_to_merge_page_tokens(this_node_page_size);
            }
        }
        self.max_allocable_page_size.unwrap()
    }

    #[rr::only_spec]
    /// Recursively traverses the tree to reach a node that contains the page token of the requested size and returns this page token. This
    /// function returns also a set of page size that are not allocable anymore at the node. This method has the max depth of recusrive
    /// invocation equal to the number of PageSize variants. This method has an upper bounded computation complexity.
    ///
    #[rr::params("memly" : "memory_layout")]
    /// Precondition: The size and base address arguments match the logical state.
    #[rr::requires("this_node_base_address = self.cur.(base_address)")]
    #[rr::requires("this_node_page_size = self.cur.(max_node_size)")]
    /// Precondition: The global memory layout is initialized.
    #[rr::requires(#iris "once_initialized π \"MEMORY_LAYOUT\" (Some memly)")]
    /// Postcondition: This node has been changed...
    #[rr::exists("node'")]
    #[rr::observe("self.ghost": "node'")]
    /// Postcondition: the size and base address remain unchanged
    #[rr::ensures("node'.(max_node_size) = self.cur.(max_node_size)")]
    #[rr::ensures("node'.(base_address) = self.cur.(base_address)")]
    /// Postcondition: The function succeeds and returns a page iff the allocable page size of the
    /// node is at least the required page size.
    #[rr::ok]
    #[rr::requires("∃ sz, page_node_can_allocate self.cur = Some sz ∧ page_size_to_acquire ≤ₚ sz")]
    /// Postcondition: if it succeeds, the returned page has the desired size.
    #[rr::ensures("ret.(page_sz) = page_size_to_acquire")]
    fn acquire_page_token(
        &mut self, this_node_base_address: usize, this_node_page_size: PageSize, page_size_to_acquire: PageSize,
    ) -> Result<Page<UnAllocated>, Error> {
        ensure!(self.max_allocable_page_size >= Some(page_size_to_acquire), Error::OutOfPages())?;
        if this_node_page_size == page_size_to_acquire {
            // End of recursion, we found the node from which we acquire a page token.
            assert!(self.page_token.is_some());
            let page_token = self.acquire_page_token_from_this_node();
            assert!(this_node_base_address == page_token.start_address());
            assert!(this_node_page_size == page_token.size());
            Ok(page_token)
        } else {
            // We are too high in the tree, i.e., the current level represents page size allocations that are larger than the page size
            // that was requested.
            assert!(this_node_page_size.smaller().is_some());
            // Lazily initialize children
            self.initialize_children_if_needed(this_node_page_size);

            // Because we are looking for a page token of a smaller size, we must divide the page token owned by this node, if that has
            // not yet occured.
            self.divide_page_token_if_necessary(this_node_base_address, this_node_page_size);

            // Let's get the index of the first child that has requested allocation.
            // This will succeed because we already checked above that the desired size can be acquired.
            let index = vec_iter(&self.children)
                .position(
                    #[rr::only_spec]
                    #[rr::returns("bool_decide ((Some {page_size_to_acquire}) ≤o{ option_cmp page_size_cmp } page_node_can_allocate node)")]
                    |node| node.max_allocable_page_size >= Some(page_size_to_acquire),
                )
                .unwrap();

            let (child_base_address, child_page_size) = self.child_address_and_size(this_node_base_address, this_node_page_size, index);
            // Invoke recursively this function to traverse to a node containing a page token of the requested size.
            // The below unwrap is ok because we found an index of a node that has requested allocation.
            let page_token = vec_index_mut(&mut self.children, index)
                .acquire_page_token(child_base_address, child_page_size, page_size_to_acquire)
                .unwrap();
            // Let's refresh information about the largest allocable page size available in children.
            self.max_allocable_page_size = vec_iter(&self.children)
                .map(
                    #[rr::returns("page_node_can_allocate child")]
                    |child| child.max_allocable_page_size,
                )
                .max()
                .flatten();
            Ok(page_token)
        }
    }

    #[rr::only_spec]
    /// Creates children for the given node because the node gets created with an empty list of children, expecting that children will be
    /// created lazily with this function.
    ///
    /// Precondition the page size argument has to match the node's logical state.
    #[rr::requires("this_node_page_size = self.cur.(max_node_size)")]
    /// Postcondition: leaves the page node unchanged except for initializing the children if necessary
    #[rr::observe("self.ghost": "mk_page_node self.cur.(max_node_size) self.cur.(base_address) self.cur.(allocation_state) true")]
    fn initialize_children_if_needed(&mut self, this_node_page_size: PageSize) {
        if self.children.is_empty() {
            self.children = (0..this_node_page_size.number_of_smaller_pages())
                .map(
                    // I think to handle this well I'll need invariants on closures.
                    // i.e., the address and so on need to become logical components of the type (even
                    // though they don't have a physical representation)
                    #[rr::skip]
                    #[rr::params("base_address", "node_size")]
                    #[rr::requires("(page_size_align node_size | base_address)%Z")]
                    #[rr::returns("mk_page_node node_size base_address PageTokenUnavailable false")]
                    |_| Self::empty(),
                )
                .collect();
        }
    }

    /// Stores the given page token in the current node.
    ///
    /// Invariant: if there is page token then all page size equal or lower than the page token are allocable from this node.
    ///
    /// Precondition: the token's size is equal to this node's size
    #[rr::requires("self.cur.(max_node_size) = page_token.(page_sz)")]
    /// Precondition: the token's address matches the node's address
    #[rr::requires("self.cur.(base_address) = page_token.(page_loc).2")]
    /// Postcondition: the node changes to the available state
    #[rr::observe("self.ghost": "mk_page_node self.cur.(max_node_size) self.cur.(base_address) PageTokenAvailable self.cur.(children_initialized)")]
    fn store_page_token_in_this_node(&mut self, page_token: Page<UnAllocated>) {
        // TODO: add back the assert!
        //assert!(self.page_token.is_none());
        self.max_allocable_page_size = Some(page_token.size());
        self.page_token = Some(page_token);
    }

    /// Returns an ownership of a page token that has been stored in this node.
    ///
    /// Precondition: The token in this node is fully available.
    #[rr::requires("Hstate" : "self.cur.(allocation_state) = PageTokenAvailable")]
    /// Postcondition: The returned token's size matches the node's size.
    #[rr::ensures("ret.(page_sz) = self.cur.(max_node_size)")]
    /// Postcondition: The returned token's address matches the node's address.
    #[rr::ensures("ret.(page_loc).2 = self.cur.(base_address)")]
    /// Postcondition: The node has been updated to the unavailable state.
    #[rr::observe("self.ghost": "mk_page_node self.cur.(max_node_size) self.cur.(base_address) PageTokenUnavailable self.cur.(children_initialized)")]
    fn acquire_page_token_from_this_node(&mut self) -> Page<UnAllocated> {
        assert!(self.page_token.is_some());
        self.max_allocable_page_size = None;
        self.page_token.take().unwrap()
    }

    /// Divides the page token into smaller page tokens.
    #[rr::params("smaller_size", "memly" : "memory_layout")]
    /// Precondition: The global memory layout is initialized.
    #[rr::requires(#iris "once_initialized π \"MEMORY_LAYOUT\" (Some memly)")]
    /// Precondition: The argument base address and size match the node's logical state.
    #[rr::requires("self.cur.(base_address) = this_node_base_address")]
    #[rr::requires("self.cur.(max_node_size) = this_node_page_size")]
    /// Precondition: The children are initialized.
    #[rr::requires("self.cur.(children_initialized)")]
    /// Precondition: There is a smaller node size.
    #[rr::requires("page_size_smaller self.cur.(max_node_size) = Some smaller_size")]
    /// Postcondition: The node is updated, being able to allocate at most [smaller_size].
    #[rr::observe("self.ghost": "mk_page_node self.cur.(max_node_size) self.cur.(base_address) (self.cur.(allocation_state) ⊓ PageTokenPartiallyAvailable smaller_size) true")]
    fn divide_page_token_if_necessary(&mut self, this_node_base_address: usize, this_node_page_size: PageSize) {
        if let Some(token) = self.page_token.take() {
            let smaller_pages = token.divide();
            assert!(smaller_pages.len() == self.children.len());

            let children = &mut self.children;
            for smaller_page_token in smaller_pages {
                #[rr::params("γ", "children_init")]
                #[rr::inv_vars("children")]
                #[rr::inv("children.ghost = γ")]
                #[rr::inv(
                    "children.cur = ((λ node, page_node_update_state node PageTokenAvailable) <$> (take (length {Hist}) children_init)) ++ drop (length {Hist}) children_init"
                )]
                #[rr::ignore]
                #[allow(unused)]
                || {};
                let index = Self::calculate_child_index(this_node_base_address, this_node_page_size, &smaller_page_token);
                vec_index_mut(children, index).store_page_token_in_this_node(smaller_page_token);
            }
            let smaller_size = this_node_page_size.smaller().unwrap();
            self.max_allocable_page_size = Some(smaller_size);
        }
    }

    #[rr::only_spec]
    /// Merges page tokens owned by children.
    /// Safety: Requires that all children have been initialized.
    ///
    /// Precondition: The children are initialized.
    #[rr::requires("self.cur.(children_initialized)")]
    /// Precondition: the argument page size matches the node's page size
    #[rr::requires("this_node_page_size = self.cur.(max_node_size)")]
    /// Postcondition: this node has been updated to a new state.
    #[rr::exists("state'")]
    #[rr::observe("self.ghost": "mk_page_node self.cur.(max_node_size) self.cur.(base_address) state' true")]
    /// Postcondition: the state is either unchanged, or the whole node is available now.
    #[rr::ensures("state' = self.cur.(allocation_state) ∨ state' = PageTokenAvailable")]
    unsafe fn try_to_merge_page_tokens(&mut self, this_node_page_size: PageSize) {
        if self.children.iter().all(
            #[rr::returns("bool_decide (child.(allocation_state) = PageTokenAvailable)")]
            |child| child.page_token.is_some(),
        ) {
            // All children have page tokens, thus we can merge them.
            let pages_to_merge = self.children.iter_mut().map(
                    // postcondition of the closure has the observation.
                    // iter_mut hands out mutable borrows. 
                    // Options: 
                    // - we immediately return the obsevation to the base iterator and allow it to
                    // resolve, 
                    // - or we collect a bigsep of observations and resolve it at the end.
                    //
                    // We might want to create the list gnames already at the very beginning when
                    // creating the iterator via iter_mut. 
                    // We can keep the observations as part of the invariant, I suppose.
                    // Then we finally get the completed invariant, and the observation of having
                    // turned the vector into a list of PlaceGhost.
                    // At this point, resolve everything. 
                    #[rr::requires("child.cur.(allocation_state) = PageTokenAvailable")]
                    #[rr::ensures("ret.(page_sz) = child.cur.(max_node_size)")]
                    #[rr::ensures("ret.(page_loc).2 = child.cur.(base_address)")]
                    #[rr::observe("child.ghost": "mk_page_node child.cur.(max_node_size) child.cur.(base_address) PageTokenUnavailable child.cur.(children_initialized)")]
                    |child| child.acquire_page_token_from_this_node()
                    ).collect();
            // Safety: Safe, because all children are initialized and have a page token available.
            self.store_page_token_in_this_node(unsafe { Page::merge(pages_to_merge, this_node_page_size) });
            self.max_allocable_page_size = Some(this_node_page_size);
        }
    }

    /// Returns the index of a child that can store the page token.
    #[rr::params("child_node_sz")]
    /// Precondition: There is a smaller page size.
    #[rr::requires("Hchild": "page_size_smaller this_node_page_size = Some child_node_sz")]
    /// Precondition: The token's page size is smaller than this node's size.
    #[rr::requires("Hsz_lt": "page_token.(page_sz) ≤ₚ child_node_sz")]
    /// Precondition: The token is within the range of this node.
    #[rr::requires("Hrange": "page_within_range this_node_base_address this_node_page_size page_token")]
    #[rr::requires("Hdiv": "page_size_in_bytes_Z this_node_page_size | this_node_base_address")]
    /// Postcondition: such that there is a matching child
    #[rr::ensures("ret < page_size_multiplier this_node_page_size")]
    /// Postcondition: The page is within the range of the child node.
    #[rr::ensures("page_within_range (this_node_base_address + ret * page_size_in_bytes_Z child_node_sz) child_node_sz page_token")]
    fn calculate_child_index(this_node_base_address: usize, this_node_page_size: PageSize, page_token: &Page<UnAllocated>) -> usize {
        assert!(this_node_page_size > page_token.size());
        let index = (page_token.start_address() - this_node_base_address) / this_node_page_size.smaller().unwrap().in_bytes();
        index
    }

    /// Returns the base address and the page size of the child at the given index
    ///
    /// Invariant: children have been created
    #[rr::params("child_node_size")]
    /// Precondition: The base address and page size arguments match the node's logical state.
    #[rr::requires("this_node_base_address = self.(base_address)")]
    #[rr::requires("this_node_page_size = self.(max_node_size)")]
    /// The children are initialized
    #[rr::requires("H_child_init": "self.(children_initialized)")]
    /// There exist children
    #[rr::requires("page_size_smaller self.(max_node_size) = Some child_node_size")]
    /// Precondition: the child index is in range
    #[rr::requires("Hindex": "index < page_size_multiplier self.(max_node_size)")]
    /// Postcondition: Returns a tuple of the child's base address and its size.
    #[rr::returns("*[child_base_address self.(base_address) child_node_size index; child_node_size] ")]
    fn child_address_and_size(&self, this_node_base_address: usize, this_node_page_size: PageSize, index: usize) -> (usize, PageSize) {
        assert!(index < self.children.len());
        assert!(this_node_page_size.smaller().is_some());
        let child_base_address = this_node_base_address + index * this_node_page_size.smaller().unwrap().in_bytes();
        let child_page_size = this_node_page_size.smaller().unwrap();
        (child_base_address, child_page_size)
    }
}

/// These wrappers serve as a temporary workaround until RefinedRust supports unsized types and in
/// particular slices: the indexing and iteration methods on `Vec` work by dereferencing to slices,
/// which currently are not supported by RefinedRust.
/// For now, we thus create wrappers for these methods to which we can attach RefinedRust
/// specifications.
mod wrappers {
    use alloc::vec::Vec;

    #[rr::only_spec]
    #[rr::requires("index < length x.cur")]
    #[rr::exists("γi")]
    #[rr::returns("(x.cur !!! Z.to_nat index, γi)")]
    #[rr::observe("x.ghost": "<[Z.to_nat index := PlaceGhost γi]> (<$#> x.cur)")]
    pub fn vec_index_mut<T>(x: &mut Vec<T>, index: usize) -> &mut T {
        &mut x[index]
    }

    #[rr::only_spec]
    #[rr::returns("x")]
    pub fn vec_iter<T>(x: &Vec<T>) -> core::slice::Iter<'_, T> {
        x.iter()
    }
}
use wrappers::*;
