// SPDX-FileCopyrightText: 2026 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

use super::locked::Locked;
use alloc::alloc::{GlobalAlloc, Layout};
use core::ptr;

/// The minimal possible allocation unit represented by a single bit in the leaf level.
pub const MIN_ALLOC_SIZE: usize = 16;

/// Total number of tree levels (L0 to L4, supports heaps up to 16 GiB).
pub const NUM_LEVELS: usize = 5;

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
    } else {
        (4, 1, 256 * 1024 * 1024)
    }
}

/// Finds an aligned contiguous run of `bits` ones in a 64-bit word.
///
/// `bits` must be a power of two in {1, 2, 4, 8, 16, 32, 64}.
/// Natural alignment is enforced: the starting bit position is a multiple of `bits`.
fn find_aligned_free_bits(word: usize, bits: usize) -> Option<usize> {
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
            if word == !0usize {
                Some(0)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// A 64-way multi-level bitmap heap allocator using safe `usize` slices.
///
/// Bit convention:
/// - `1` = Free / subtree contains at least one free block.
/// - `0` = Allocated / full / unavailable.
pub struct BitmapAllocator {
    heap_start: usize,
    heap_end: usize,
    total_blocks: usize,
    initialized: bool,
    l0: &'static mut [usize],
    l1: &'static mut [usize],
    l2: &'static mut [usize],
    l3: &'static mut [usize],
    l4: &'static mut [usize],
}

impl BitmapAllocator {
    /// Creates an uninitialized empty BitmapAllocator with zero BSS overhead.
    pub const fn empty() -> Self {
        Self {
            heap_start: 0,
            heap_end: 0,
            total_blocks: 0,
            initialized: false,
            l0: &mut [],
            l1: &mut [],
            l2: &mut [],
            l3: &mut [],
            l4: &mut [],
        }
    }

    /// Initializes the bitmap allocator over the given heap address range.
    ///
    /// The metadata slices are placed dynamically at the start of the provided memory region,
    /// requiring `< 0.8%` of heap memory, with zero static `.bss` consumption.
    pub fn init(&mut self, start_address: usize, heap_size: usize) {
        debug!("Initializing BitmapAllocator at 0x{:x} with size {} bytes", start_address, heap_size);
        if heap_size < 4096 {
            return;
        }

        // Calculate metadata word requirements
        let max_blocks = heap_size / MIN_ALLOC_SIZE;
        let l0_len = (max_blocks + 63) / 64;
        let l1_len = (l0_len + 63) / 64;
        let l2_len = (l1_len + 63) / 64;
        let l3_len = (l2_len + 63) / 64;
        let l4_len = (l3_len + 63) / 64;
        let total_meta_words = l0_len + l1_len + l2_len + l3_len + l4_len;
        let meta_bytes = total_meta_words * core::mem::size_of::<usize>();
        let meta_bytes_aligned = (meta_bytes + 1023) & !1023;

        if meta_bytes_aligned >= heap_size {
            return;
        }

        let data_start = start_address + meta_bytes_aligned;
        let data_size = (start_address + heap_size).saturating_sub(data_start);
        let total_blocks = data_size / MIN_ALLOC_SIZE;
        if total_blocks == 0 {
            return;
        }

        // Carve metadata slice from heap start and zero it
        let meta_slice: &'static mut [usize] = unsafe { core::slice::from_raw_parts_mut(start_address as *mut usize, total_meta_words) };
        meta_slice.fill(0);

        // Split into level slices
        let (l0, rest) = meta_slice.split_at_mut(l0_len);
        let (l1, rest) = rest.split_at_mut(l1_len);
        let (l2, rest) = rest.split_at_mut(l2_len);
        let (l3, l4) = rest.split_at_mut(l3_len);

        // Populate Level 0 (1 bit = 16 B)
        let full_l0 = total_blocks / 64;
        for i in 0..full_l0.min(l0.len()) {
            l0[i] = !0usize;
        }
        let rem_l0 = total_blocks % 64;
        if rem_l0 > 0 && full_l0 < l0.len() {
            l0[full_l0] = (1usize << rem_l0) - 1;
        }

        // Build Level 1 (1 bit = 1 KiB)
        let num_l0 = (total_blocks + 63) / 64;
        let full_l1 = num_l0 / 64;
        for i in 0..full_l1.min(l1.len()) {
            l1[i] = !0usize;
        }
        let rem_l1 = num_l0 % 64;
        if rem_l1 > 0 && full_l1 < l1.len() {
            l1[full_l1] = (1usize << rem_l1) - 1;
        }

        // Build Level 2 (1 bit = 64 KiB)
        let num_l1 = (num_l0 + 63) / 64;
        let full_l2 = num_l1 / 64;
        for i in 0..full_l2.min(l2.len()) {
            l2[i] = !0usize;
        }
        let rem_l2 = num_l1 % 64;
        if rem_l2 > 0 && full_l2 < l2.len() {
            l2[full_l2] = (1usize << rem_l2) - 1;
        }

        // Build Level 3 (1 bit = 4 MiB)
        let num_l2 = (num_l1 + 63) / 64;
        let full_l3 = num_l2 / 64;
        for i in 0..full_l3.min(l3.len()) {
            l3[i] = !0usize;
        }
        let rem_l3 = num_l2 % 64;
        if rem_l3 > 0 && full_l3 < l3.len() {
            l3[full_l3] = (1usize << rem_l3) - 1;
        }

        // Build Level 4 (1 bit = 256 MiB)
        let num_l3 = (num_l2 + 63) / 64;
        let rem_l4 = num_l3 % 64;
        if rem_l4 > 0 && !l4.is_empty() {
            l4[0] = (1usize << rem_l4) - 1;
        }

        self.heap_start = data_start;
        self.heap_end = data_start + total_blocks * MIN_ALLOC_SIZE;
        self.total_blocks = total_blocks;
        self.l0 = l0;
        self.l1 = l1;
        self.l2 = l2;
        self.l3 = l3;
        self.l4 = l4;
        self.initialized = true;
    }

    #[inline(always)]
    fn get_node(&self, level: usize, idx: usize) -> usize {
        match level {
            0 => self.l0.get(idx).copied().unwrap_or(0),
            1 => self.l1.get(idx).copied().unwrap_or(0),
            2 => self.l2.get(idx).copied().unwrap_or(0),
            3 => self.l3.get(idx).copied().unwrap_or(0),
            4 => self.l4.get(idx).copied().unwrap_or(0),
            _ => 0,
        }
    }

    #[inline(always)]
    fn set_node(&mut self, level: usize, idx: usize, val: usize) {
        match level {
            0 => {
                if let Some(slot) = self.l0.get_mut(idx) {
                    *slot = val;
                }
            }
            1 => {
                if let Some(slot) = self.l1.get_mut(idx) {
                    *slot = val;
                }
            }
            2 => {
                if let Some(slot) = self.l2.get_mut(idx) {
                    *slot = val;
                }
            }
            3 => {
                if let Some(slot) = self.l3.get_mut(idx) {
                    *slot = val;
                }
            }
            4 => {
                if let Some(slot) = self.l4.get_mut(idx) {
                    *slot = val;
                }
            }
            _ => {}
        }
    }

    #[inline(always)]
    fn level_len(&self, level: usize) -> usize {
        match level {
            0 => self.l0.len(),
            1 => self.l1.len(),
            2 => self.l2.len(),
            3 => self.l3.len(),
            4 => self.l4.len(),
            _ => 0,
        }
    }

    fn is_subtree_completely_free(&self, level: usize, node_idx: usize) -> bool {
        if level == 0 {
            self.get_node(0, node_idx) == !0usize
        } else {
            if self.get_node(level, node_idx) != !0usize {
                return false;
            }
            let start_child = node_idx * 64;
            let end_child = (start_child + 64).min(self.level_len(level - 1));
            for child_idx in start_child..end_child {
                if !self.is_subtree_completely_free(level - 1, child_idx) {
                    return false;
                }
            }
            true
        }
    }

    fn set_subtree(&mut self, level: usize, node_idx: usize, free: bool) {
        let val = if free { !0usize } else { 0 };
        self.set_node(level, node_idx, val);
        if level > 0 {
            let start_child = node_idx * 64;
            let end_child = (start_child + 64).min(self.level_len(level - 1));
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
                    let mask = if req_bits == 64 { !0usize } else { ((1usize << req_bits) - 1) << bit_pos };
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
                    if child_idx < self.level_len(level - 1) {
                        if self.is_subtree_completely_free(level - 1, child_idx) {
                            self.set_subtree(level - 1, child_idx, false);
                            let new_word = self.get_node(level, node_idx) & !(1usize << bit_pos);
                            self.set_node(level, node_idx, new_word);

                            let blocks_per_child = 1usize << (level * 6);
                            return Some(child_idx * blocks_per_child);
                        }
                    }
                    word &= !(1usize << bit_pos);
                }
                return None;
            }
        }

        // Descend to lower levels
        let mut word = self.get_node(level, node_idx);
        while word != 0 {
            let bit_pos = word.trailing_zeros() as usize;
            let child_idx = node_idx * 64 + bit_pos;
            if child_idx < self.level_len(level - 1) {
                if let Some(block_idx) = self.alloc_from_node(level - 1, child_idx, req_level, req_bits) {
                    if self.get_node(level - 1, child_idx) == 0 {
                        let new_word = self.get_node(level, node_idx) & !(1usize << bit_pos);
                        self.set_node(level, node_idx, new_word);
                    }
                    return Some(block_idx);
                }
            }
            word &= !(1usize << bit_pos);
        }
        None
    }

    fn propagate_up(&mut self, mut level: usize, mut node_idx: usize) {
        while level + 1 <= 4 {
            let parent_level = level + 1;
            let parent_idx = node_idx / 64;
            let bit_pos = node_idx % 64;

            if parent_idx >= self.level_len(parent_level) {
                break;
            }

            let old_parent = self.get_node(parent_level, parent_idx);
            let new_parent = old_parent | (1usize << bit_pos);
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
            let mask = if req_bits == 64 { !0usize } else { ((1usize << req_bits) - 1) << bit_pos };
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
            let new_val = old_val | (1usize << bit_pos);
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
        if req_level > 4 {
            return ptr::null_mut();
        }

        let root_level = 4;
        for node_idx in 0..self.level_len(root_level) {
            if let Some(block_idx) = self.alloc_from_node(root_level, node_idx, req_level, req_bits) {
                if block_idx * MIN_ALLOC_SIZE + layout.size() <= self.total_blocks * MIN_ALLOC_SIZE {
                    return (self.heap_start + block_idx * MIN_ALLOC_SIZE) as *mut u8;
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
        if ptr_val < self.heap_start || ptr_val >= self.heap_end {
            return;
        }

        let offset = ptr_val - self.heap_start;
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
