// SPDX-FileCopyrightText: 2026 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

use super::locked::Locked;
use crate::core::memory_layout::ConfidentialMemoryAddress;
use crate::error::Error;
use alloc::alloc::{GlobalAlloc, Layout};
use core::ptr;
use pointers_utility::ptr_byte_add_mut;

pub const MIN_ALLOC_SIZE: usize = 16;
pub const NUM_LEVELS: usize = 5; // L0 (16B), L1 (1KiB), L2 (64KiB), L3 (4MiB), L4 (256MiB)

/// Generates a bitmask with `count` consecutive 1-bits shifted by `shift`.
fn bit_mask(count: usize, shift: usize) -> usize {
    if count >= usize::BITS as usize { !0usize } else { ((1usize << count) - 1) << shift }
}

/// Maps layout to tree level and intra-word power-of-2 bit count: (level, bits).
fn allocation_target(layout: Layout) -> (usize, usize) {
    let size = layout.size().max(layout.align()).max(MIN_ALLOC_SIZE);
    let total_blocks = (size + MIN_ALLOC_SIZE - 1) / MIN_ALLOC_SIZE;
    let mut blocks = total_blocks.next_power_of_two();
    let mut level = 0;
    while blocks > 32 && level + 1 < NUM_LEVELS {
        blocks = (blocks + 63) / 64;
        level += 1;
    }
    (level, blocks.min(64))
}

/// Finds an aligned contiguous run of `bits` ones in a 64-bit word.
fn find_aligned_bits(word: usize, bits: usize) -> Option<usize> {
    if word == 0 {
        return None;
    }
    if bits == 1 {
        return Some(word.trailing_zeros() as usize);
    }
    let mask = (1usize << bits) - 1;
    for pos in (0..usize::BITS as usize).step_by(bits) {
        if (word >> pos) & mask == mask {
            return Some(pos);
        }
    }
    None
}

/// A 64-way multi-level bitmap heap allocator.
pub struct BitmapAllocator {
    data_start: usize,
    levels: [&'static mut [usize]; NUM_LEVELS],
}

impl BitmapAllocator {
    pub const fn new() -> Self {
        Self { data_start: 0, levels: [&mut [], &mut [], &mut [], &mut [], &mut []] }
    }

    pub fn init(&mut self, start_address: ConfidentialMemoryAddress, end_address: ConfidentialMemoryAddress) -> Result<(), Error> {
        let heap_size = end_address.as_usize().saturating_sub(start_address.as_usize());
        debug!(
            "Initializing BitmapAllocator from 0x{:x} to 0x{:x} ({} bytes)",
            start_address.as_usize(),
            end_address.as_usize(),
            heap_size
        );

        // Calculate metadata requirements and slice partitions
        let max_blocks = heap_size / MIN_ALLOC_SIZE;
        let mut level_lens = [0usize; NUM_LEVELS];
        let mut active = max_blocks;
        let mut total_words = 0;
        for lvl in 0..NUM_LEVELS {
            level_lens[lvl] = (active + 63) / 64;
            total_words += level_lens[lvl];
            active = level_lens[lvl];
        }

        let meta_bytes = (total_words * core::mem::size_of::<usize>() + MIN_ALLOC_SIZE - 1) & !(MIN_ALLOC_SIZE - 1);
        ensure!(meta_bytes < heap_size, Error::NotEnoughMemory())?;

        let raw_start = start_address.to_mut_ptr_usize();
        let end_bound = end_address.to_mut_ptr_usize() as *const usize;
        let data_start_ptr = ptr_byte_add_mut(raw_start, meta_bytes, end_bound).map_err(|_| Error::InvalidMemoryBoundary())?;

        // Initialize metadata memory from heap start preserving provenance
        let meta_slice: &'static mut [usize] = unsafe { core::slice::from_raw_parts_mut(raw_start, total_words) };
        meta_slice.fill(0);

        let mut rest = meta_slice;
        for lvl in 0..NUM_LEVELS {
            let (slice, remaining) = rest.split_at_mut(level_lens[lvl]);
            self.levels[lvl] = slice;
            rest = remaining;
        }

        // Populate free bits bottom-up
        let mut active_bits = (heap_size - meta_bytes) / MIN_ALLOC_SIZE;
        for lvl in 0..NUM_LEVELS {
            let full_words = active_bits / 64;
            let rem_bits = active_bits % 64;
            self.levels[lvl][..full_words].fill(!0usize);
            if rem_bits > 0 {
                self.levels[lvl][full_words] = (1usize << rem_bits) - 1;
            }
            active_bits = (active_bits + 63) / 64;
        }

        self.data_start = data_start_ptr.addr();
        Ok(())
    }

    fn set_subtree(&mut self, level: usize, node_idx: usize, val: usize) {
        if let Some(slot) = self.levels[level].get_mut(node_idx) {
            *slot = val;
            if level > 0 {
                let start = node_idx * 64;
                let end = (start + 64).min(self.levels[level - 1].len());
                for child in start..end {
                    self.set_subtree(level - 1, child, val);
                }
            }
        }
    }

    fn is_subtree_free(&self, level: usize, node_idx: usize) -> bool {
        if self.levels[level].get(node_idx).copied() != Some(!0usize) {
            return false;
        }
        if level == 0 {
            return true;
        }
        let start = node_idx * 64;
        let end = (start + 64).min(self.levels[level - 1].len());
        (start..end).all(|child| self.is_subtree_free(level - 1, child))
    }

    fn are_children_free(&self, level: usize, start: usize, count: usize) -> bool {
        let end = start + count;
        end <= self.levels[level].len() && (start..end).all(|child| self.is_subtree_free(level, child))
    }

    fn propagate_bit(&mut self, mut level: usize, mut node_idx: usize, set_free: bool) {
        while level + 1 < NUM_LEVELS {
            let parent_level = level + 1;
            let parent_idx = node_idx / 64;
            let bit = 1usize << (node_idx % 64);

            let old_parent = self.levels[parent_level][parent_idx];
            let new_parent = if set_free { old_parent | bit } else { old_parent & !bit };
            self.levels[parent_level][parent_idx] = new_parent;

            if if set_free { old_parent != 0 } else { new_parent != 0 } {
                break;
            }

            level = parent_level;
            node_idx = parent_idx;
        }
    }

    fn modify_block(&mut self, level: usize, node_idx: usize, bit_pos: usize, bits: usize, set_free: bool) {
        if level > 0 {
            let subtree_val = if set_free { !0usize } else { 0 };
            let start_child = node_idx * 64 + bit_pos;
            for child in start_child..(start_child + bits) {
                self.set_subtree(level - 1, child, subtree_val);
            }
        }

        let mask = bit_mask(bits, bit_pos);
        let old_word = self.levels[level][node_idx];
        let new_word = if set_free { old_word | mask } else { old_word & !mask };
        self.levels[level][node_idx] = new_word;

        let transitioned = if set_free { old_word == 0 } else { new_word == 0 };
        if transitioned {
            self.propagate_bit(level, node_idx, set_free);
        }
    }

    fn claim(&mut self, level: usize, node_idx: usize, req_bits: usize) -> Option<usize> {
        let mut word = self.levels[level].get(node_idx).copied()?;
        while let Some(bit_pos) = find_aligned_bits(word, req_bits) {
            let start_child = node_idx * 64 + bit_pos;
            if level == 0 || self.are_children_free(level - 1, start_child, req_bits) {
                self.modify_block(level, node_idx, bit_pos, req_bits, false);
                return Some(start_child << (level * 6));
            }
            word &= !bit_mask(req_bits, bit_pos);
        }
        None
    }

    fn alloc_from_node(&mut self, level: usize, node_idx: usize, req_level: usize, req_bits: usize) -> Option<usize> {
        if level == req_level {
            return self.claim(level, node_idx, req_bits);
        }

        let mut word = self.levels[level].get(node_idx).copied()?;
        while word != 0 {
            let bit_pos = word.trailing_zeros() as usize;
            let child_idx = node_idx * 64 + bit_pos;
            if child_idx < self.levels[level - 1].len() {
                if let Some(block_idx) = self.alloc_from_node(level - 1, child_idx, req_level, req_bits) {
                    return Some(block_idx);
                }
            }
            word &= !(1usize << bit_pos);
        }
        None
    }

    fn dealloc_block(&mut self, block_idx: usize, req_level: usize, req_bits: usize) {
        let start_node = block_idx >> (req_level * 6);
        self.modify_block(req_level, start_node / 64, start_node % 64, req_bits, true);
    }

    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        if self.data_start == 0 {
            return ptr::null_mut();
        }
        let (req_level, req_bits) = allocation_target(layout);
        let root = NUM_LEVELS - 1;
        for node in 0..self.levels[root].len() {
            if let Some(block) = self.alloc_from_node(root, node, req_level, req_bits) {
                return ptr::without_provenance_mut(self.data_start + block * MIN_ALLOC_SIZE);
            }
        }
        ptr::null_mut()
    }

    pub fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        if ptr.is_null() || self.data_start == 0 {
            return;
        }
        let offset = ptr.addr().saturating_sub(self.data_start);
        let (req_level, req_bits) = allocation_target(layout);
        self.dealloc_block(offset / MIN_ALLOC_SIZE, req_level, req_bits);
    }
}

unsafe impl GlobalAlloc for Locked<BitmapAllocator> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.size() == 0 {
            return ptr::without_provenance_mut(layout.align());
        }
        self.lock().alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if layout.size() == 0 {
            return;
        }
        self.lock().dealloc(ptr, layout);
    }
}
