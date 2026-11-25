// Segregated-Free List (intrusive)
// Summary:
//  - Initially, allocations are handled by a bump-allocator.
//  - On deallocation, allocations end up in a segregated free-list
//  - Once allocated memory regions never change their size
// -> Heap memory is dynamically partitioned trough allocations
//
//
// `alloc` picks the smallest size class that fits the allocation. If that class has a free block, it is popped from the list.
// Otherwise a new block is taken from a bump allocator (one pointer to free memory, advanced on allocation, no dealloc).
// `dealloc` pushes the block onto the list of its class. There is no splitting and no coalescing: once a region is
// allocated, it keeps its size forever.
//
// Once a memory region was allocated, it can have two states:
// - Allocated: (no intrusive data structure exists, region contains data)
// - Deallocated: First bytes are used for the intrusive data structure.
//
// Potential limitations:
// - No padding supported: Maximum requested alignment of 16 is assumed.
// - Possible requested sizes need to be known.
// - Potential performance improvement: One mutex per free list and one for the bump allocator (might not be worth it)

use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout};
use crate::error::Error;
use alloc::alloc::{GlobalAlloc, Layout};
use core::mem::{align_of, size_of};
use core::ptr::null_mut;
use spin::{Mutex, Once};

// Block sizes in bytes, sorted. Sizes found by static analysis.
const SIZE_CLASSES: [usize; 13] = [48, 64, 192, 2048, 4096, 6144, 8192, 8208, 12288, 24576, 32784, 49152, 264368];
const NUMBER_OF_SIZE_CLASSES: usize = SIZE_CLASSES.len();

// All class sizes are multiples of this, so every block stays aligned to it without padding.
const BLOCK_ALIGNMENT: usize = 16;
// Ends a free list.
const NO_BLOCK: usize = usize::MAX;
const NOT_A_HEAP_BLOCK: &str = "Bug. The heap allocator got back memory it never handed out";

// Checked at compile time, so editing the table cannot break the invariants.
const _: () = {
    assert!(BLOCK_ALIGNMENT.is_multiple_of(align_of::<usize>()));
    let mut class = 0;
    while class < NUMBER_OF_SIZE_CLASSES {
        assert!(SIZE_CLASSES[class].is_multiple_of(BLOCK_ALIGNMENT));
        // assert all size classes fit into the intrusive data structure:
        assert!(SIZE_CLASSES[class] >= size_of::<usize>());
        assert!(class == 0 || SIZE_CLASSES[class - 1] < SIZE_CLASSES[class]);
        class += 1;
    }
};

pub struct SegregatedAllocator {
    heap: Once<Mutex<SizeClassHeap>>,
}

impl SegregatedAllocator {
    pub const fn empty() -> Self {
        Self { heap: Once::new() }
    }

    // May only be called once
    pub unsafe fn add_memory_region(
        &self, memory_region_start: ConfidentialMemoryAddress, memory_region_end: *const usize,
    ) -> Result<(), Error> {
        // heap is initialized only once
        ensure_not!(self.heap.is_completed(), Error::Reinitialization())?;
        // alignment of start
        ensure!(memory_region_start.is_aligned_to(BLOCK_ALIGNMENT), Error::InvalidMemoryBoundary())?;

        // check confidential memory address
        let memory_layout = MemoryLayout::read();
        ensure!(
            memory_layout.confidential_address_at_offset_bounded(&memory_region_start, 0, memory_region_end).is_ok(),
            Error::InvalidMemoryBoundary()
        )?;

        // initialize heap
        let heap = SizeClassHeap::new(memory_region_start, memory_region_end);
        self.heap.call_once(|| Mutex::new(heap));
        Ok(())
    }
}

unsafe impl GlobalAlloc for SegregatedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let Some(heap) = self.heap.get() else { return null_mut() };
        match heap.lock().allocate(layout) {
            Some(block) => block.to_ptr().cast_mut(),
            None => null_mut(),
        }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        self.heap.get().expect(NOT_A_HEAP_BLOCK).lock().deallocate(pointer.addr(), layout);
    }
}

// All offsets are relative to start (ConfidentialMemoryAddress).
// Some possible invariants:
// - start is aligned to BLOCK_ALIGNMENT
// - heap "owns" `[start, end)
// - [start + unused, end) was never returned by alloc
// - free_lists[x] content is one of the following:
//   - NO_BLOCK: value for empty list
//   - <head>: offset of a free block of SIZE_CLASSES[x] bytes, whose first word holds the offset of the next free block of that class.
// - all blocks are disjoint (no overlaps)
// - blocks are in [start, start + unused)
// - unused <= end - start
// - unused % BLOCK_ALIGNMENT == 0
struct SizeClassHeap {
    start: ConfidentialMemoryAddress,
    end: *const usize,
    unused: usize,
    free_lists: [usize; NUMBER_OF_SIZE_CLASSES],
}

unsafe impl Send for SizeClassHeap {}

impl SizeClassHeap {
    fn new(start: ConfidentialMemoryAddress, end: *const usize) -> Self {
        Self { start, end, unused: 0, free_lists: [NO_BLOCK; NUMBER_OF_SIZE_CLASSES] }
    }

    fn allocate(&mut self, layout: Layout) -> Option<ConfidentialMemoryAddress> {
        if layout.align() > BLOCK_ALIGNMENT {
            // limitation: no special alignemnts supported right now.
            return None;
        }
        let class = size_class_of(layout.size())?;

        // check free list of class
        if let Some(block) = self.pop_free_block(class) {
            return Some(block);
        }

        // free list was empty, use bump allocator
        self.take_unused_memory(SIZE_CLASSES[class])
    }

    // precondition: address was once returned by self.take_unused_memory in self.allocate
    fn deallocate(&mut self, address: usize, layout: Layout) {
        // replace usize addr by pointer
        let class = size_class_of(layout.size()).expect(NOT_A_HEAP_BLOCK);
        let offset = address.checked_sub(self.start.as_usize()).expect(NOT_A_HEAP_BLOCK);
        let block = self.block_at(offset).expect(NOT_A_HEAP_BLOCK);

        // insert old head as next pointer
        unsafe { block.write_volatile(self.free_lists[class]) };
        // replace old head
        self.free_lists[class] = offset;
    }

    // takes a block from the free-list of class
    fn pop_free_block(&mut self, class: usize) -> Option<ConfidentialMemoryAddress> {
        let head = self.free_lists[class];
        if head == NO_BLOCK {
            // empty
            return None;
        }
        let block: ConfidentialMemoryAddress = self.block_at(head)?;

        // remove this block from the free-list and replace it by the address written in block
        self.free_lists[class] = unsafe { block.read_volatile() };
        Some(block)
    }

    fn take_unused_memory(&mut self, size: usize) -> Option<ConfidentialMemoryAddress> {
        let block = self.block_at(self.unused)?;
        // check if remaining memory is sufficient
        self.block_at(self.unused.checked_add(size - 1)?)?;
        self.unused += size;
        Some(block)
    }

    // Turns an offset into an address
    fn block_at(&self, offset: usize) -> Option<ConfidentialMemoryAddress> {
        MemoryLayout::read().confidential_address_at_offset_bounded(&self.start, offset, self.end).ok()
    }
}

// Index of the smallest class that fits. None if largest size class is too small.
fn size_class_of(size: usize) -> Option<usize> {
    // could be improved. E.g. array lookup for "fast path".
    let mut class = 0;
    while class < NUMBER_OF_SIZE_CLASSES {
        if size <= SIZE_CLASSES[class] {
            return Some(class);
        }
        class += 1;
    }
    None
}
