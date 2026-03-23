// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

//! # Heap Allocator Module
//!
//! Provides memory allocation for the security monitor's heap.
//!
//! ## Implementation: Buddy Allocator
//!
//! This module uses a buddy system allocator that provides:
//! - **Zero external fragmentation** through automatic coalescing
//! - **Bounded O(log n) latency** suitable for real-time systems
//! - **Formal verification compatibility** with simple, deterministic logic
//!
//! See `buddy_allocator.rs` for detailed design documentation.

use crate::core::memory_layout::ConfidentialMemoryAddress;

pub mod buddy_allocator;
pub use buddy_allocator::LockedBuddyAllocator;

/// Global allocator instance for the security monitor heap
#[global_allocator]
static HEAP_ALLOCATOR: LockedBuddyAllocator = LockedBuddyAllocator::new();

/// Initializes the heap allocator with a memory region
///
/// # Arguments
///
/// * `start_address` - The start of the heap memory region
/// * `heap_size` - The size of the heap memory region in bytes
///
/// # Safety
///
/// Must be called exactly once during system initialization with a valid,
/// unused memory region.
///
/// # Time Complexity
/// O(1) - Only initializes free list with initial pool
///
/// # Panics
///
/// Will panic in debug mode if called more than once.
pub unsafe fn init_heap(start_address: ConfidentialMemoryAddress, heap_size: usize) {
    debug!(
        "Initializing buddy allocator heap: {:x}-{:x}",
        start_address.as_usize(),
        start_address.as_usize() + heap_size
    );
    HEAP_ALLOCATOR.init(start_address.as_usize(), heap_size);
}

/// Returns diagnostic information about allocator state (debug only)
///
/// Returns the total number of free blocks across all free lists.
/// Useful for monitoring fragmentation and heap health.
///
/// # Examples
///
/// ```ignore
/// #[cfg(debug_assertions)]
/// {
///     let free_blocks = debug_heap_stats();
///     debug!("Free blocks: {}", free_blocks);
/// }
/// ```
#[cfg(debug_assertions)]
pub fn debug_heap_stats() -> usize {
    HEAP_ALLOCATOR.free_block_count()
}
