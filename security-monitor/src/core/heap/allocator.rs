// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-FileContributor: Heavily based on https://os.phil-opp.com/allocator-designs/
// SPDX-License-Identifier: Apache-2.0
use core::alloc::{GlobalAlloc, Layout};
use core::mem;

pub type MemoryAllocator = Locked<LinkedListAllocator>;

pub struct LinkedListAllocator {
    head: ListNode,
}

// This is a temporal allocator implementation that will be replaced in the future with a safer version.
impl LinkedListAllocator {
    pub const fn empty() -> Self {
        Self { head: ListNode::new(0) }
    }

    pub fn add_free_region(&mut self, base_address: *const u8, size: usize) {
        // assert_eq!(align_up(addr, mem::align_of::<ListNode>()), addr);
        if size < mem::size_of::<ListNode>() {
            return;
        }
        let mut free_node = ListNode::new(size);
        free_node.next = self.head.next.take();
        self.head.next = unsafe {
            // Safety: casting to *mut ListNode is fine because we checked in the beginning
            // of this function that the given memory region is larger than the size
            // of a ListNode
            let node_pointer = base_address as *mut ListNode;
            node_pointer.write(free_node);
            Some(&mut *node_pointer)
        }
    }

    pub fn find_region(&mut self, size: usize, align: usize) -> Option<(&'static mut ListNode, *mut u8)> {
        let mut current = &mut self.head;
        while let Some(ref mut region) = current.next {
            if let Ok(alloc_start) = Self::alloc_from_region(region, size, align) {
                let next = region.next.take();
                let ret = Some((current.next.take().unwrap(), alloc_start));
                current.next = next;
                return ret;
            } else {
                current = current.next.as_mut().unwrap();
            }
        }
        None
    }

    pub fn alloc_from_region(region: &mut ListNode, size_in_bytes: usize, align: usize) -> Result<*mut u8, ()> {
        let offset_to_align = region.start_address_pointer().align_offset(align);
        let alloc_start = unsafe { region.start_address_pointer().add(offset_to_align) };
        let alloc_end = unsafe { alloc_start.byte_add(size_in_bytes) };

        let free_space_left = unsafe { region.end_addr().byte_offset_from(alloc_end) };
        if free_space_left < 0 {
            // region too small
            return Err(());
        }
        let excess_size = unsafe { region.end_addr().byte_offset_from(alloc_end) };
        if excess_size > 0 && excess_size < (mem::size_of::<ListNode>() as isize) {
            // rest of region too small to hold a ListNode (required because the
            // allocation splits the region in a used and a free part)
            return Err(());
        }
        // region suitable for allocation
        Ok(alloc_start)
    }

    pub fn size_align(layout: Layout) -> (usize, usize) {
        let layout = layout.align_to(mem::align_of::<ListNode>()).expect("adjusting alignment failed").pad_to_align();
        let size = layout.size().max(mem::size_of::<ListNode>());
        (size, layout.align())
    }
}

pub struct ListNode {
    size: usize,
    pub next: Option<&'static mut ListNode>,
}

impl ListNode {
    pub const fn new(size: usize) -> Self {
        ListNode { size, next: None }
    }

    pub fn start_address_pointer(&mut self) -> *mut u8 {
        self as *mut _ as *mut u8
    }

    pub fn end_addr(&self) -> *const u8 {
        let start_address = self as *const _ as *const u8;
        unsafe { start_address.byte_add(self.size) }
    }
}

unsafe impl GlobalAlloc for MemoryAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.try_alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let (size, _) = LinkedListAllocator::size_align(layout);
        self.lock().add_free_region(ptr, size)
    }
}

impl MemoryAllocator {
    pub const fn empty() -> Self {
        Locked::new(LinkedListAllocator::empty())
    }

    fn try_alloc(&self, layout: Layout) -> *mut u8 {
        if let Some(address) = self.alloc_dynamic(layout) {
            return address;
        } else {
            debug!("Heap allocation failed. No more pages in the memory tracker");
            panic!("run out of memory");
        }
    }

    fn alloc_dynamic(&self, layout: Layout) -> Option<*mut u8> {
        // perform layout adjustments
        let (size, align) = LinkedListAllocator::size_align(layout);
        let mut allocator = self.lock();

        if let Some((region, alloc_start)) = allocator.find_region(size, align) {
            let alloc_end = unsafe { alloc_start.byte_add(size) };
            let free_space_left = unsafe { region.end_addr().byte_offset_from(alloc_end) };
            if let Ok(size) = usize::try_from(free_space_left) {
                allocator.add_free_region(alloc_end, size);
            }
            Some(alloc_start)
        } else {
            None
        }
    }
}

pub struct Locked<A> {
    inner: spin::Mutex<A>,
}

impl<A> Locked<A> {
    pub const fn new(inner: A) -> Self {
        Locked { inner: spin::Mutex::new(inner) }
    }

    pub fn lock(&self) -> spin::MutexGuard<A> {
        self.inner.lock()
    }
}
