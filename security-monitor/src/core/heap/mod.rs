// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use allocator::MemoryAllocator;

mod allocator;

// This object allocates memory on the security monitor's heap.
#[global_allocator]
static mut HEAP_ALLOCATOR: MemoryAllocator = MemoryAllocator::empty();

pub(super) fn init_heap(start_address: *mut usize, heap_size: usize) {
    debug!("Heap {:x}-{:x}", start_address as usize, (start_address as usize) + heap_size);
    unsafe {
        HEAP_ALLOCATOR.lock().add_free_memory_region(start_address, heap_size);
    }
}
