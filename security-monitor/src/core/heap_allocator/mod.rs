// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialMemoryAddress;
use allocator::{LinkedListAllocator, Locked};

mod allocator;

/// global allocator allocates memory on the security monitor's heap.
#[global_allocator]
static HEAP_ALLOCATOR: Locked<LinkedListAllocator> = Locked::new(LinkedListAllocator::new());

pub(super) fn init_heap(start_address: ConfidentialMemoryAddress, heap_size: usize) {
    debug!("Heap {:x}-{:x}", start_address.as_usize(), start_address.as_usize() + heap_size);
    unsafe {
        HEAP_ALLOCATOR.lock().add_free_region(start_address.as_usize(), heap_size);
    }
}
