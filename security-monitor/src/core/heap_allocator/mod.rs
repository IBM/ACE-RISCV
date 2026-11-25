// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialMemoryAddress;
use crate::error::Error;
use allocator::LockedLinkedListAllocator as HeapAllocator;

mod allocator;

/// global allocator allocates memory on the security monitor's heap.
#[global_allocator]
static HEAP_ALLOCATOR: HeapAllocator = HeapAllocator::empty();

pub(super) fn init_heap(memory_start: ConfidentialMemoryAddress, memory_end: *const usize) -> Result<(), Error> {
    debug!("Heap {:x}-{:x}", memory_start.as_usize(), memory_end.addr());
    unsafe { HEAP_ALLOCATOR.add_memory_region(memory_start, memory_end) }
}
