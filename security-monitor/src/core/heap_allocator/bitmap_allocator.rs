// SPDX-FileCopyrightText: 2026 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

use super::locked::Locked;
use alloc::alloc::{GlobalAlloc, Layout};
use core::ptr;

/// The minimal possible allocation unit represented by a single bit in the leaf level.
pub const MIN_ALLOC_SIZE: usize = 16;

/// Maximum number of tree levels (supports up to 64 GiB heaps with 64-way branching).
pub const MAX_LEVELS: usize = 6;

fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

/// Computes the allocation parameters for a given requested `Layout`.
///
/// Returns `(req_level, req_bits, bucket_size)`:
/// - For intra-L0 sizes (16 B .. 512 B): `req_level = 0`, `req_bits = bucket_size / 16`.
/// - For inter-level sizes (1 KiB, 64 KiB, 4 MiB, etc.): `req_level >= 1`, `req_bits = 1`.
fn get_allocation_params(layout: Layout) -> (usize, usize, usize) {
    let size = layout.size().max(layout.align()).max(MIN_ALLOC_SIZE);

    if size <= 16 {
        (0, 1, 16)
    } else if size <= 32 {
        (0, 2, 32)
    } else if size <= 64 {
        (0, 4, 64)
    } else if size <= 128 {
        (0, 8, 128)
    } else if size <= 256 {
        (0, 16, 256)
    } else if size <= 512 {
        (0, 32, 512)
    } else if size <= 1024 {
        (1, 1, 1024)
    } else if size <= 64 * 1024 {
        (2, 1, 64 * 1024)
    } else if size <= 4 * 1024 * 1024 {
        (3, 1, 4 * 1024 * 1024)
    } else if size <= 256 * 1024 * 1024 {
        (4, 1, 256 * 1024 * 1024)
    } else {
        (5, 1, 16 * 1024 * 1024 * 1024)
    }
}

/// Finds an aligned contiguous run of `bits` ones in a 64-bit word.
///
/// `bits` must be a power of two in {1, 2, 4, 8, 16, 32, 64}.
/// Natural alignment is enforced: the starting bit position is a multiple of `bits`.
fn find_aligned_free_bits(word: u64, bits: usize) -> Option<usize> {
    if word == 0 {
        return None;
    }
    match bits {
        1 => Some(word.trailing_zeros() as usize),
        2 => {
            let candidates = word & (word >> 1) & 0x5555_5555_5555_5555;
            if candidates != 0 { Some(candidates.trailing_zeros() as usize) } else { None }
        }
        4 => {
            let c2 = word & (word >> 1);
            let candidates = c2 & (c2 >> 2) & 0x1111_1111_1111_1111;
            if candidates != 0 { Some(candidates.trailing_zeros() as usize) } else { None }
        }
        8 => {
            let c2 = word & (word >> 1);
            let c4 = c2 & (c2 >> 2);
            let candidates = c4 & (c4 >> 4) & 0x0101_0101_0101_0101;
            if candidates != 0 { Some(candidates.trailing_zeros() as usize) } else { None }
        }
        16 => {
            let c2 = word & (word >> 1);
            let c4 = c2 & (c2 >> 2);
            let c8 = c4 & (c4 >> 4);
            let candidates = c8 & (c8 >> 8) & 0x0001_0001_0001_0001;
            if candidates != 0 { Some(candidates.trailing_zeros() as usize) } else { None }
        }
        32 => {
            let c2 = word & (word >> 1);
            let c4 = c2 & (c2 >> 2);
            let c8 = c4 & (c4 >> 4);
            let c16 = c8 & (c8 >> 8);
            let candidates = c16 & (c16 >> 16) & 0x0000_0001_0000_0001;
            if candidates != 0 { Some(candidates.trailing_zeros() as usize) } else { None }
        }
        64 => {
            if word == !0u64 {
                Some(0)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// A 64-way multi-level bitmap heap allocator.
///
/// - Level 0: 1 bit = 16 bytes. Each `u64` covers 1 KiB ($64 \times 16\text{ B}$).
/// - Level 1: 1 bit = 1 KiB (covers one L0 node). Each `u64` covers 64 KiB ($64 \times 1\text{ KiB}$).
/// - Level 2: 1 bit = 64 KiB. Each `u64` covers 4 MiB.
/// - Level 3: 1 bit = 4 MiB. Each `u64` covers 256 MiB.
/// - Level 4: 1 bit = 256 MiB. Each `u64` covers 16 GiB.
/// - Level 5: 1 bit = 16 GiB. Each `u64` covers 1 TiB.
///
/// Bit convention:
/// - `1` = Free / subtree contains at least one free block.
/// - `0` = Allocated / full / unavailable.
pub struct BitmapAllocator {
    data_start: usize,
    data_size: usize,
    total_blocks: usize,
    num_levels: usize,
    level_offsets: [usize; MAX_LEVELS],
    level_lens: [usize; MAX_LEVELS],
    metadata_ptr: *mut u64,
    initialized: bool,
}

unsafe impl Send for BitmapAllocator {}

impl BitmapAllocator {
    /// Creates an uninitialized empty BitmapAllocator.
    pub const fn empty() -> Self {
        Self {
            data_start: 0,
            data_size: 0,
            total_blocks: 0,
            num_levels: 0,
            level_offsets: [0; MAX_LEVELS],
            level_lens: [0; MAX_LEVELS],
            metadata_ptr: ptr::null_mut(),
            initialized: false,
        }
    }

    /// Initializes the bitmap allocator over the provided memory region.
    ///
    /// The metadata (multi-level bitmap tree) is placed at the start of the memory region,
    /// and the remaining memory is used as the allocatable heap data space.
    pub unsafe fn init(&mut self, heap_start: usize, heap_size: usize) {
        debug!("Initializing BitMap allocator at address: 0x{:x} with size {}", heap_start, heap_size);
        if heap_size < 1024 {
            return;
        }

        // Estimate upper bound for metadata words
        let max_blocks = heap_size / MIN_ALLOC_SIZE;
        let mut est_words = 0;
        let mut count = (max_blocks + 63) / 64;
        while count > 0 {
            est_words += count;
            if count <= 1 {
                break;
            }
            count = (count + 63) / 64;
        }

        let meta_bytes_aligned = align_up(est_words * core::mem::size_of::<u64>(), 1024);
        if meta_bytes_aligned >= heap_size {
            return;
        }

        let data_start = align_up(heap_start + meta_bytes_aligned, 1024);
        if data_start >= heap_start + heap_size {
            return;
        }

        let data_size = (heap_start + heap_size) - data_start;
        let total_blocks = data_size / MIN_ALLOC_SIZE;
        if total_blocks == 0 {
            return;
        }

        // Calculate exact level lengths and offsets
        let mut l_lens = [0usize; MAX_LEVELS];
        let mut l_offs = [0usize; MAX_LEVELS];

        l_lens[0] = (total_blocks + 63) / 64;
        let mut curr_offset = 0;
        l_offs[0] = curr_offset;
        curr_offset += l_lens[0];

        let mut levels = 1;
        for lvl in 1..MAX_LEVELS {
            if l_lens[lvl - 1] > 1 {
                l_lens[lvl] = (l_lens[lvl - 1] + 63) / 64;
                l_offs[lvl] = curr_offset;
                curr_offset += l_lens[lvl];
                levels = lvl + 1;
            } else {
                break;
            }
        }

        let metadata_ptr = heap_start as *mut u64;
        let metadata_len = curr_offset;

        // Zero all metadata words first
        for i in 0..metadata_len {
            unsafe { *metadata_ptr.add(i) = 0 };
        }

        self.data_start = data_start;
        self.data_size = data_size;
        self.total_blocks = total_blocks;
        self.num_levels = levels;
        self.level_offsets = l_offs;
        self.level_lens = l_lens;
        self.metadata_ptr = metadata_ptr;
        self.initialized = true;

        // Initialize Level 0 bits (1 = Free)
        for i in 0..self.level_lens[0] {
            let val = if (i + 1) * 64 <= total_blocks {
                !0u64
            } else if i * 64 < total_blocks {
                let rem = total_blocks - (i * 64);
                if rem >= 64 { !0u64 } else { (1u64 << rem) - 1 }
            } else {
                0u64
            };
            self.set_node(0, i, val);
        }

        // Build higher levels from bottom to top
        for lvl in 1..self.num_levels {
            for node_idx in 0..self.level_lens[lvl] {
                let mut word = 0u64;
                for bit in 0..64 {
                    let child_idx = node_idx * 64 + bit;
                    if child_idx < self.level_lens[lvl - 1] {
                        if self.get_node(lvl - 1, child_idx) != 0 {
                            word |= 1u64 << bit;
                        }
                    }
                }
                self.set_node(lvl, node_idx, word);
            }
        }
    }

    #[inline(always)]
    fn get_node(&self, level: usize, node_idx: usize) -> u64 {
        let offset = self.level_offsets[level] + node_idx;
        unsafe { *self.metadata_ptr.add(offset) }
    }

    #[inline(always)]
    fn set_node(&mut self, level: usize, node_idx: usize, val: u64) {
        let offset = self.level_offsets[level] + node_idx;
        unsafe { *self.metadata_ptr.add(offset) = val };
    }

    fn is_subtree_completely_free(&self, level: usize, node_idx: usize) -> bool {
        if level == 0 {
            self.get_node(0, node_idx) == !0u64
        } else {
            if self.get_node(level, node_idx) != !0u64 {
                return false;
            }
            let start_child = node_idx * 64;
            let end_child = (start_child + 64).min(self.level_lens[level - 1]);
            for child_idx in start_child..end_child {
                if !self.is_subtree_completely_free(level - 1, child_idx) {
                    return false;
                }
            }
            true
        }
    }

    fn set_subtree(&mut self, level: usize, node_idx: usize, free: bool) {
        let val = if free { !0u64 } else { 0 };
        self.set_node(level, node_idx, val);
        if level > 0 {
            let start_child = node_idx * 64;
            let end_child = (start_child + 64).min(self.level_lens[level - 1]);
            for child_idx in start_child..end_child {
                self.set_subtree(level - 1, child_idx, free);
            }
        }
    }

    fn alloc_from_node(&mut self, level: usize, node_idx: usize, req_level: usize, req_bits: usize) -> Option<usize> {
        if level == req_level {
            if req_level == 0 {
                let word = self.get_node(0, node_idx);
                if let Some(bit_pos) = find_aligned_free_bits(word, req_bits) {
                    let mask = if req_bits == 64 { !0u64 } else { ((1u64 << req_bits) - 1) << bit_pos };
                    let new_word = word & !mask;
                    self.set_node(0, node_idx, new_word);
                    return Some(node_idx * 64 + bit_pos);
                }
                return None;
            } else {
                let mut word = self.get_node(level, node_idx);
                while word != 0 {
                    let bit_pos = word.trailing_zeros() as usize;
                    let child_idx = node_idx * 64 + bit_pos;
                    if child_idx < self.level_lens[level - 1] {
                        if self.is_subtree_completely_free(level - 1, child_idx) {
                            self.set_subtree(level - 1, child_idx, false);
                            let new_word = self.get_node(level, node_idx) & !(1u64 << bit_pos);
                            self.set_node(level, node_idx, new_word);

                            let blocks_per_child = 1usize << (level * 6);
                            return Some(child_idx * blocks_per_child);
                        }
                    }
                    word &= !(1u64 << bit_pos);
                }
                return None;
            }
        }

        // Descend to lower levels
        let mut word = self.get_node(level, node_idx);
        while word != 0 {
            let bit_pos = word.trailing_zeros() as usize;
            let child_idx = node_idx * 64 + bit_pos;
            if child_idx < self.level_lens[level - 1] {
                if let Some(block_idx) = self.alloc_from_node(level - 1, child_idx, req_level, req_bits) {
                    if self.get_node(level - 1, child_idx) == 0 {
                        let new_word = self.get_node(level, node_idx) & !(1u64 << bit_pos);
                        self.set_node(level, node_idx, new_word);
                    }
                    return Some(block_idx);
                }
            }
            word &= !(1u64 << bit_pos);
        }
        None
    }

    fn propagate_up(&mut self, mut level: usize, mut node_idx: usize) {
        while level + 1 < self.num_levels {
            let parent_level = level + 1;
            let parent_idx = node_idx / 64;
            let bit_pos = node_idx % 64;

            if parent_idx >= self.level_lens[parent_level] {
                break;
            }

            let old_parent = self.get_node(parent_level, parent_idx);
            let new_parent = old_parent | (1u64 << bit_pos);
            self.set_node(parent_level, parent_idx, new_parent);

            if old_parent != 0 {
                break;
            }

            level = parent_level;
            node_idx = parent_idx;
        }
    }

    fn dealloc_block(&mut self, block_idx: usize, req_level: usize, req_bits: usize) {
        if req_level == 0 {
            let leaf_idx = block_idx / 64;
            let bit_pos = block_idx % 64;
            let mask = if req_bits == 64 { !0u64 } else { ((1u64 << req_bits) - 1) << bit_pos };
            let old_val = self.get_node(0, leaf_idx);
            let new_val = old_val | mask;
            self.set_node(0, leaf_idx, new_val);

            if old_val == 0 {
                self.propagate_up(0, leaf_idx);
            }
        } else {
            let blocks_per_child = 1usize << (req_level * 6);
            let child_idx = block_idx / blocks_per_child;
            self.set_subtree(req_level - 1, child_idx, true);

            let parent_idx = child_idx / 64;
            let bit_pos = child_idx % 64;
            let old_val = self.get_node(req_level, parent_idx);
            let new_val = old_val | (1u64 << bit_pos);
            self.set_node(req_level, parent_idx, new_val);

            if old_val == 0 {
                self.propagate_up(req_level, parent_idx);
            }
        }
    }

    /// Allocates memory with the given layout.
    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        if !self.initialized || self.total_blocks == 0 {
            return ptr::null_mut();
        }

        let (req_level, req_bits, _bucket_size) = get_allocation_params(layout);
        if req_level >= self.num_levels {
            return ptr::null_mut();
        }

        let root_level = self.num_levels - 1;
        for node_idx in 0..self.level_lens[root_level] {
            if let Some(block_idx) = self.alloc_from_node(root_level, node_idx, req_level, req_bits) {
                let offset = block_idx * MIN_ALLOC_SIZE;
                if offset + layout.size() <= self.data_size {
                    return (self.data_start + offset) as *mut u8;
                } else {
                    self.dealloc_block(block_idx, req_level, req_bits);
                    return ptr::null_mut();
                }
            }
        }

        ptr::null_mut()
    }

    /// Deallocates previously allocated memory.
    pub fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        if !self.initialized || ptr.is_null() {
            return;
        }

        let ptr_val = ptr as usize;
        if ptr_val < self.data_start || ptr_val >= self.data_start + self.data_size {
            return;
        }

        let offset = ptr_val - self.data_start;
        if offset % MIN_ALLOC_SIZE != 0 {
            return;
        }

        let block_idx = offset / MIN_ALLOC_SIZE;
        let (req_level, req_bits, _bucket_size) = get_allocation_params(layout);
        self.dealloc_block(block_idx, req_level, req_bits);
    }
}

unsafe impl GlobalAlloc for Locked<BitmapAllocator> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.size() == 0 {
            return layout.align() as *mut u8;
        }
        self.lock().alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if ptr.is_null() || layout.size() == 0 || ptr as usize == layout.align() {
            return;
        }
        self.lock().dealloc(ptr, layout);
    }
}
