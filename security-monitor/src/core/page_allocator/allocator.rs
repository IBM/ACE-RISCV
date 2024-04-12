// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use super::page::{Page, UnAllocated};
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout};
use crate::core::memory_protector::PageSize;
use crate::error::Error;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use spin::{Once, RwLock, RwLockWriteGuard};

/// A static global structure containing unallocated pages. Once<> guarantees that the PageAllocator can only be initialized once.
static PAGE_ALLOCATOR: Once<RwLock<PageAllocator>> = Once::new();

pub struct PageAllocator {
    base_address: usize,
    page_size: PageSize,
    root: TreeNode,
}

impl PageAllocator {
    const NOT_INITIALIZED: &'static str = "Bug. Could not access page allocator because it is not initialized";

    pub unsafe fn initialize(memory_start: ConfidentialMemoryAddress, memory_end: *const usize) -> Result<(), Error> {
        assure_not!(PAGE_ALLOCATOR.is_completed(), Error::Reinitialization())?;
        let mut page_allocator = Self::empty(memory_start.as_usize());
        page_allocator.add_memory_region(memory_start, memory_end);
        PAGE_ALLOCATOR.call_once(|| RwLock::new(page_allocator));
        Ok(())
    }

    fn empty(base_address: usize) -> Self {
        let base_address_aligned_down = (base_address - 1) & !(PageSize::largest().in_bytes() - 1);
        Self { root: TreeNode::new(), base_address: base_address_aligned_down, page_size: PageSize::largest() }
    }

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
                self.root.store_page_token(self.base_address, self.page_size, new_page_token);
            }
        }
    }

    /// Returns a page token that has ownership over an unallocated memory region of the requested size. Returns error if it could not
    /// obtain write access to the global instance of the page allocator or if there are not enough page tokens satisfying the requested
    /// criteria.
    pub fn acquire_page(page_size_to_allocate: PageSize) -> Result<Page<UnAllocated>, Error> {
        Self::try_write(|page_allocator| {
            let base_address = page_allocator.base_address;
            let page_size = page_allocator.page_size;
            Ok(page_allocator.root.acquire_page_token(base_address, page_size, page_size_to_allocate))
        })?
        .map(|(page_token, _)| page_token)
    }

    /// Consumes the page tokens given by the caller, allowing for their further acquisition. This is equivalent to deallocation of the
    /// physical memory region owned by the returned page tokens. Given vector of pages might contains pages of arbitrary sizes.
    pub fn release_pages(released_pages: Vec<Page<UnAllocated>>) {
        let _ = Self::try_write(|page_allocator| {
            let base_address = page_allocator.base_address;
            let page_size = page_allocator.page_size;
            released_pages.into_iter().for_each(|page_token| {
                page_allocator.root.store_page_token(base_address, page_size, page_token);
            });
            Ok(())
        })
        .inspect_err(|_| debug!("Memory leak: failed to store released pages in the page allocator"));
    }

    /// returns a mutable reference to the PageAllocator after obtaining a lock on the mutex
    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, PageAllocator>) -> Result<F, Error> {
        op(&mut PAGE_ALLOCATOR.get().expect(Self::NOT_INITIALIZED).write())
    }
}

struct TreeNode {
    page_token: Option<Page<UnAllocated>>,
    allocable_page_sizes: BTreeSet<PageSize>,
    children: Vec<TreeNode>,
}

impl TreeNode {
    /// Creates a node at the given addres and page size, and recursively creates all children nodes.
    pub fn new() -> Self {
        Self { page_token: None, allocable_page_sizes: BTreeSet::new(), children: vec![] }
    }

    pub fn store_page_token(&mut self, base_address: usize, page_size: PageSize, page_token: Page<UnAllocated>) -> BTreeSet<PageSize> {
        match &page_size == page_token.size() {
            true => {
                assert!(base_address == page_token.start_address());
                assert!(&page_size == page_token.size());
                self.store_page_token_in_this_node(page_token)
            }
            false => {
                // If we do not allocate all possible tree levels during initialization, we must do it lazily. This is what happens below.
                self.initialize_children_if_needed(page_size);

                // We are at the wrong level. Let's go recursively to the node where this page belongs to.
                let child_page_size = page_size.smaller().unwrap();
                let index = (page_token.start_address() - base_address) / child_page_size.in_bytes();
                let child_base_address = base_address + index * child_page_size.in_bytes();
                let mut allocable_page_sizes = self.children[index].store_page_token(child_base_address, child_page_size, page_token);

                // We are coming back from the recursion. Since the page token was stored, we might be able to merge page tokens.
                // Specifically, if every child owns a page token, then we can merge them into a page token belonging to this node.
                allocable_page_sizes.append(&mut self.merge_pages_if_needed(page_size));

                // Let's update information about allocable page sizes.
                self.allocable_page_sizes.append(&mut allocable_page_sizes.clone());
                allocable_page_sizes
            }
        }
    }

    /// Recurisvelt traverses the tree to get to a node that contains the page token of the requested size and returns this page token. This
    /// function returns also a set of page size that are not allocable anymore at the node.
    pub fn acquire_page_token(
        &mut self, base_address: usize, page_size: PageSize, page_size_to_acquire: PageSize,
    ) -> Result<(Page<UnAllocated>, BTreeSet<PageSize>), Error> {
        match &page_size == &page_size_to_acquire {
            true => {
                // End of recursion, we found the node from which we acquire a page token.
                let (page_token, not_allocable_page_sizes) = self.acquire_page_token_from_this_node();
                assert!(base_address == page_token.start_address());
                assert!(&page_size == page_token.size());
                Ok((page_token, not_allocable_page_sizes))
            }
            false => {
                // We know that it is possible to allocate the page of the given size. Check if we must divide the page at this level before
                // we go deeper in the tree.
                let mut not_allocable_page_sizes = self.divide_page_if_needed(base_address, page_size);
                // Invoke recursively this function to get to a node containing a page token of the requestd size.
                let child_page_size = page_size.smaller().unwrap();

                let index = self
                    .children
                    .iter_mut()
                    .position(|n| n.allocable_page_sizes.contains(&page_size_to_acquire))
                    .ok_or(Error::OutOfPages())?;

                let child_base_address = base_address + index * child_page_size.in_bytes();
                // below unwrap is ok since we found an index of a node that had allocation for the request page size
                let (page_token, mut not_allocable_page_sizes_from_children) =
                    self.children[index].acquire_page_token(child_base_address, child_page_size, page_size_to_acquire).unwrap();
                
                // We returned from recursion, time to update nodes with information what page sizes are allocable
                not_allocable_page_sizes.append(&mut not_allocable_page_sizes_from_children);

                // Check if the page sizes are not available in other nodes.
                for node in self.children.iter() {
                    not_allocable_page_sizes.retain(|a| !node.allocable_page_sizes.contains(a));
                    if not_allocable_page_sizes.is_empty() {
                        break;
                    }
                }
                // Since we removed a page from childrens, we must update information what page sizes are still allocable in this
                // node.
                self.allocable_page_sizes.retain(|a| !not_allocable_page_sizes.contains(a));
                Ok((page_token, not_allocable_page_sizes))
            }
        }
    }

    /// Creates a subtree for the given node.
    /// Invariant: any child of this node owns a page token
    fn initialize_children_if_needed(&mut self, page_size: PageSize) {
        if !self.children.is_empty() {
            return;
        }
        if let Some(smaller_size) = page_size.smaller() {
            let number_of_smaller_pages = page_size.in_bytes() / smaller_size.in_bytes();
            self.children = (0..number_of_smaller_pages).map(|_| TreeNode::new()).collect();
        }
    }

    /// Stores page token in the current node.
    /// Invariant: if there is page token then all page size equal or lower than the page token are allocable from this node.
    fn store_page_token_in_this_node(&mut self, page_token: Page<UnAllocated>) -> BTreeSet<PageSize> {
        assert!(self.page_token.is_none());
        self.allocable_page_sizes = page_token.size().all_equal_or_smaller();
        self.page_token = Some(page_token);
        self.allocable_page_sizes.clone()
    }

    /// Returns a page token.
    /// Invariant: if there is no page token, then there is no allocable page size in this node.
    fn acquire_page_token_from_this_node(&mut self) -> (Page<UnAllocated>, BTreeSet<PageSize>) {
        assert!(self.page_token.is_some());
        let page = self.page_token.take().unwrap();
        let allocable_page_sizes = core::mem::replace(&mut self.allocable_page_sizes, BTreeSet::new());
        (page, allocable_page_sizes)
    }

    /// Divides the page token (if exists in the node) into smaller page tokens.
    /// Invariant: page size of the divided page token is no longer allocable on this node.
    /// Invariant: every child node owns a smaller page token.
    fn divide_page_if_needed(&mut self, base_address: usize, page_size: PageSize) -> BTreeSet<PageSize> {
        let mut not_allocable_page_sizes = BTreeSet::new();
        if let Some(page_token) = self.page_token.take() {
            // We consume the page, so it will no longer be available for allocation.
            not_allocable_page_sizes.insert(page_size);
            // We divide the page into smaller ones, because the caller requested pages of smaller sizes.
            self.initialize_children_if_needed(page_size);

            let mut smaller_pages = page_token.divide();
            assert!(smaller_pages.len() == self.children.len());
            smaller_pages.drain(..).for_each(|smaller_page_token| {
                let index = (smaller_page_token.start_address() - base_address) / smaller_page_token.size().in_bytes();
                self.children[index].store_page_token_in_this_node(smaller_page_token);
            })
        }
        not_allocable_page_sizes
    }

    /// Merges page tokens owned by children, only if every child owns a page token. Returns a set of page sizes that
    /// can be allocated at the current node after merging.
    /// Invariant: after merging, any child ownes a page token
    /// Invariant: after merging, this node owns a page token corresopnding to the given size and can allocate pages of the given size or
    /// smaller.
    fn merge_pages_if_needed(&mut self, larger_page_size: PageSize) -> BTreeSet<PageSize> {
        // Right now, we need two full iterations, could we these both passes into one iteration?
        match self.children.iter().all(|child| child.page_token.is_some()) {
            true => {
                let pages_to_merge = self.children.iter_mut().map(|child| child.acquire_page_token_from_this_node().0).collect();
                self.store_page_token_in_this_node(unsafe { Page::merge(pages_to_merge, larger_page_size) })
            }
            false => BTreeSet::new(),
        }
    }
}
