// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-FileContributor: Heavily based on https://os.phil-opp.com/allocator-designs/
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use core::alloc::{GlobalAlloc, Layout};
use core::mem;
use pointers_utility::{ptr_align, ptr_byte_add_mut, ptr_byte_offset};

///! TODO: This is a temporal allocator implementation that will be replaced in the future with a version that
///! is safer and prevents fragmentation.

pub type HeapAllocator = Locked<LinkedListAllocator>;

pub struct LinkedListAllocator {
    head: FreeMemoryRegion,
}

impl LinkedListAllocator {
    pub(self) const fn empty() -> Self {
        Self { head: FreeMemoryRegion::new(0) }
    }

    // TODO: We should merge continous chunks of memory to prevent fragmentation. Fragmentation
    // can lead to the situation where the heap allocator no longer allows allocating larger chunks of memory
    // because the free memory is fragmented into to small chunks.
    pub fn add_free_memory_region(&mut self, base_address: *const usize, size: usize) {
        assert!(size < isize::MAX.try_into().unwrap());
        assert!(base_address.is_aligned_to(mem::align_of::<FreeMemoryRegion>()));
        if 0 < size && size < mem::size_of::<FreeMemoryRegion>() {
            debug!("Memory leak?");
            // Potential memory leak? To make sure there are no memory leaks here, we must guarantee that we
            // never allocate chunks smaller than the size of a FreeMemoryRegion structure
        }

        let mut free_node = FreeMemoryRegion::new(size);
        free_node.next = self.head.next.take();
        // Safety: casting to *mut FreeMemoryRegion is fine because the caller is giving the ownership
        // of this memory region to us.
        let node_pointer = base_address as *mut FreeMemoryRegion;
        if node_pointer.is_null() {
            debug!("problem with null node pointer in heap allocator");
        } else {
            // Safety: we can write the whole FreeMemoryRegion because we checked in the beginning of this
            // function that the memory region has enough space to hold the FreeMemoryRegion.
            self.head.next = unsafe {
                node_pointer.write(free_node);
                Some(&mut *node_pointer)
            }
        }
    }

    pub(self) fn find_free_memory_region(&mut self, size: usize, align: usize) -> Option<(*mut usize, *mut usize, usize)> {
        let mut current = &mut self.head;
        while let Some(ref mut region) = current.next {
            if let Ok((alloc_start, alloc_end, free_space_left)) = region.try_allocation(size, align) {
                current.next = region.next.take();
                let ret = Some((alloc_start, alloc_end, free_space_left));
                return ret;
            } else {
                current = current.next.as_mut().unwrap();
            }
        }
        None
    }
}

struct FreeMemoryRegion {
    size: usize,
    pub next: Option<&'static mut FreeMemoryRegion>,
}

impl FreeMemoryRegion {
    pub const fn new(size: usize) -> Self {
        Self { size, next: None }
    }

    pub fn start_address_ptr(&mut self) -> *mut usize {
        self as *mut _ as *mut usize
    }

    pub fn end_address_ptr(&self) -> *const usize {
        let start_address = self as *const _ as *const usize as usize;
        (start_address + self.size) as *const usize
    }

    // TODO: this function should return three disjoined continous memory regions if allocation is possible
    // One region would represent the allocation, and two other the remaining free memory.
    pub(self) fn try_allocation(&mut self, size_in_bytes: usize, align_in_bytes: usize) -> Result<(*mut usize, *mut usize, usize), Error> {
        let alloc_start = ptr_align(self.start_address_ptr(), align_in_bytes, self.end_address_ptr())?;
        let alloc_end = ptr_byte_add_mut(alloc_start, size_in_bytes, self.end_address_ptr())?;

        // We only allow allocating from the given region if there is enough space to reuse the resulting space for a
        // FreeMemoryRegion
        let free_space_left = ptr_byte_offset(self.end_address_ptr(), alloc_end);
        ensure!(free_space_left == 0 || free_space_left >= (mem::size_of::<FreeMemoryRegion>() as isize), Error::OutOfMemory())?;

        Ok((alloc_start, alloc_end, free_space_left as usize))
    }

    pub(self) fn align_to(layout: Layout) -> (usize, usize) {
        let layout = layout.align_to(mem::align_of::<FreeMemoryRegion>()).unwrap().pad_to_align();
        let size = layout.size().max(mem::size_of::<FreeMemoryRegion>());
        (size, layout.align())
    }
}

unsafe impl GlobalAlloc for HeapAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let layout = if layout.size() < mem::size_of::<FreeMemoryRegion>() {
            Layout::from_size_align(mem::size_of::<FreeMemoryRegion>(), layout.align()).unwrap()
        } else {
            layout
        };
        self.try_alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let (size, _) = FreeMemoryRegion::align_to(layout);
        if !ptr.is_null() && size > 0 {
            self.lock().add_free_memory_region(ptr as *mut usize, size);
        } else {
            debug!("Problem in dealloc. Null or zero size {}", size);
        }
    }
}

impl HeapAllocator {
    pub const fn empty() -> Self {
        Locked::new(LinkedListAllocator::empty())
    }

    fn try_alloc(&self, layout: Layout) -> *mut u8 {
        match self.alloc_dynamic(layout) {
            Some(address) => address,
            None => {
                debug!("Heap allocation failed. Could not add more memory to the heap because there are no more free pages in the page allocator");
                panic!("Out of memory");
            }
        }
    }

    fn alloc_dynamic(&self, layout: Layout) -> Option<*mut u8> {
        let (size, align) = FreeMemoryRegion::align_to(layout);
        let mut allocator = self.lock();
        allocator.find_free_memory_region(size, align).and_then(|(alloc_start, alloc_end, free_space_left)| {
            allocator.add_free_memory_region(alloc_end, free_space_left);
            Some(alloc_start as *mut u8)
        })
    }
}

pub struct Locked<A> {
    inner: spin::Mutex<A>,
}

impl<A> Locked<A> {
    pub(self) const fn new(inner: A) -> Self {
        Locked { inner: spin::Mutex::new(inner) }
    }

    pub fn lock(&self) -> spin::MutexGuard<A> {
        self.inner.lock()
    }
}
