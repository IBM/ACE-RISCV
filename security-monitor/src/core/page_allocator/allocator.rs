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
        Self { root: TreeNode::new(base_address_aligned_down, PageSize::largest()) }
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
                self.root.store_page_token(new_page_token);
            }
        }
    }

    /// Returns a page token that has ownership over an unallocated memory region of the requested size. Returns error if it could not
    /// obtain write access to the global instance of the page allocator or if there are not enough page tokens satisfying the requested
    /// criteria.
    pub fn acquire_page(page_size: PageSize) -> Result<Page<UnAllocated>, Error> {
        Self::try_write(|page_allocator| Ok(page_allocator.root.acquire_page_token(page_size)))?.map(|(a, b)| a)
    }

    /// Consumes the page tokens given by the caller, allowing for their further acquisition. This is equivalent to deallocation of the
    /// physical memory region owned by the returned page tokens. Given vector of pages might contains pages of arbitrary sizes.
    pub fn release_pages(released_pages: Vec<Page<UnAllocated>>) {
        let _ = Self::try_write(|page_allocator| {
            released_pages.into_iter().for_each(|page| {
                page_allocator.root.store_page_token(page);
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
    base_address: usize,
    page_size: PageSize,
    page_token: Option<Page<UnAllocated>>,
    allocable_page_sizes: BTreeSet<PageSize>,
    children: Vec<TreeNode>,
}

impl TreeNode {
    /// Creates a node at the given addres and page size, and recursively creates all children nodes.
    pub fn new(base_address: usize, page_size: PageSize) -> Self {
        Self { base_address, page_size, page_token: None, allocable_page_sizes: BTreeSet::new(), children: vec![] }
    }

    pub fn store_page_token(&mut self, page_token: Page<UnAllocated>) -> BTreeSet<PageSize> {
        match &self.page_size == page_token.size() {
            true => self.store_page_token_in_this_node(page_token),
            false => {
                // If we do not allocate all possible tree levels during initialization, we must do it lazily. This is what happens below.
                self.initialize_children_if_needed();

                // We are at the wrong level. Let's go recursively to the node where this page belongs to.
                let index = (page_token.start_address() - self.base_address) / self.page_size.smaller().unwrap().in_bytes();
                let mut allocable_page_sizes = self.children[index].store_page_token(page_token);

                // We are coming back from the recursion. Since the page token was stored, we might be able to merge page tokens.
                // Specifically, if every child owns a page token, then we can merge them into a page token belonging to this node.
                allocable_page_sizes.append(&mut self.merge_pages_if_needed());

                // Let's update information about allocable page sizes.
                self.allocable_page_sizes.append(&mut allocable_page_sizes.clone());
                allocable_page_sizes
            }
        }
    }

    /// Recurisvelt traverses the tree to get to a node that contains the page token of the requested size and returns this page token. This
    /// function returns also a set of page size that are not allocable anymore at the node.
    pub fn acquire_page_token(&mut self, page_size: PageSize) -> Result<(Page<UnAllocated>, BTreeSet<PageSize>), Error> {
        match &self.page_size == &page_size {
            true => Ok(self.acquire_page_token_from_this_node()),
            false => {
                // We know that it is possible to allocate the page of the given size. Check if we must divide the page at this level before
                // we go deeper in the tree.
                let mut not_allocable_page_sizes = self.divide_page_if_needed();
                // Invoke recursively this function to get to a node containing a page token of the requestd size.
                self.children
                    .iter_mut()
                    .find(|n| n.allocable_page_sizes.contains(&page_size))
                    .ok_or(Error::OutOfPages())?
                    .acquire_page_token(page_size)
                    .and_then(|(page_token, mut not_allocable_page_sizes_from_children)| {
                        //
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
                    })
            }
        }
    }

    /// Creates a subtree for the given node.
    fn initialize_children_if_needed(&mut self) {
        if !self.children.is_empty() {
            return;
        }
        if let Some(smaller_size) = self.page_size.smaller() {
            let number_of_smaller_pages = self.page_size.in_bytes() / smaller_size.in_bytes();
            (0..number_of_smaller_pages).for_each(|index| {
                let smaller_page_base_address = self.base_address + index * smaller_size.in_bytes();
                self.children.push(TreeNode::new(smaller_page_base_address, smaller_size));
            });
        }
    }

    /// Stores page token in the current node.
    fn store_page_token_in_this_node(&mut self, page_token: Page<UnAllocated>) -> BTreeSet<PageSize> {
        assert!(self.base_address == page_token.start_address());
        assert!(&self.page_size == page_token.size());
        self.allocable_page_sizes = page_token.size().all_equal_or_smaller();
        self.page_token = Some(page_token);
        self.allocable_page_sizes.clone()
    }

    /// Returns a page token. Maintains an invariant that when there is no page token, then there is no allocable page size.
    fn acquire_page_token_from_this_node(&mut self) -> (Page<UnAllocated>, BTreeSet<PageSize>) {
        assert!(self.page_token.is_some());
        let page = self.page_token.take().unwrap();
        let allocable_page_sizes = core::mem::replace(&mut self.allocable_page_sizes, BTreeSet::new());
        (page, allocable_page_sizes)
    }

    fn divide_page_if_needed(&mut self) -> BTreeSet<PageSize> {
        let mut not_allocable_page_sizes = BTreeSet::new();
        if let Some(page_token) = self.page_token.take() {
            // We consume the page, so it will no longer be available for allocation.
            not_allocable_page_sizes.insert(self.page_size);
            // We divide the page into smaller ones, because the caller requested pages of smaller sizes.
            self.initialize_children_if_needed();

            let mut smaller_pages = page_token.divide();
            assert!(smaller_pages.len() == self.children.len());
            smaller_pages.drain(..).for_each(|smaller_page_token| {
                let index = (smaller_page_token.start_address() - self.base_address) / smaller_page_token.size().in_bytes();
                self.children[index].store_page_token_in_this_node(smaller_page_token);
            })
        }
        not_allocable_page_sizes
    }

    /// Merges page tokens stored at the lower level, if all page tokens at the lower level are available. Returns a set of page sizes that
    /// can be allocated at the current node after merging.
    fn merge_pages_if_needed(&mut self) -> BTreeSet<PageSize> {
        // We can merge only if there are all pages at the lower level.
        // Right now, we need two full iterations, could we these both passes into one iteration?
        let mut allocable_page_sizes = BTreeSet::new();
        if self.children.iter().all(|child| child.page_token.is_some()) {
            let pages_to_merge = self
                .children
                .iter_mut()
                .map(|child| {
                    child.allocable_page_sizes.clear();
                    // unwrap is ok because we checked that there are all pages
                    child.page_token.take().unwrap()
                })
                .collect();
            self.page_token = Some(unsafe { Page::merge(pages_to_merge, self.page_size) });
            allocable_page_sizes = self.page_size.all_equal_or_smaller();
        }
        allocable_page_sizes
    }
}
