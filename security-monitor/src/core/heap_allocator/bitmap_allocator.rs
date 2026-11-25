// SPDX-FileCopyrightText: 2026 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

//! A heap allocator that tracks free memory with a tree of bitmaps.
//!
//! # The picture
//!
//! The heap is cut into small *blocks* of `MIN_ALLOC_SIZE` bytes. The tree has `NUM_LEVELS` levels.
//! Every node of the tree is one `usize` word, and every word has 64 bits.
//!
//! * Level 0 (the *leaves*) has one bit per block. Bit = 1 means "this block is free".
//! * On level 1 and above, one bit stands for one word of the level below (its *child*). That bit is 1 if the child
//!   word still has at least one free block somewhere below it, and 0 otherwise.
//! * So one bit on level `l` covers `64^l` blocks.
//!
//! # Well-formed tree (WF)
//!
//! The tree is *well-formed* when all of the following hold:
//!
//! 1. **Shape.** Level `l+1` has exactly one bit for every word of level `l`, so it has `ceil(words(l) / 64)` words.
//! 2. **Leaves are the truth.** A leaf bit is 1 if and only if its block is free. Leaf bits that do not correspond
//!    to any block of the heap (padding at the end) are always 0.
//! 3. **Summaries are exact.** A bit on level 1 or above is 1 if and only if the child word it points to is not
//!    zero. A bit that points to a child word that does not exist is 0.
//!
//! Rule 3 means the upper levels carry no information of their own. They are a copy of the leaves, squeezed so that
//! the search can skip big empty areas quickly. Given the leaves, there is exactly one way to fill the upper levels.
//! The set of free blocks is therefore defined by level 0 alone.
//!
//! # Words used in the contracts
//!
//! * **Real block**: a block that is part of the heap. There are `N` of them, numbered `0 .. N`. The leaf bits
//!   `N ..` at the end of level 0 are padding and are always 0.
//! * **Free set**: the set of real blocks whose leaf bit is 1. Contracts describe what happens to this set.
//! * **Range** `[first, first + count)`: the blocks `first`, `first + 1`, ..., `first + count - 1`.
//! * **WF**: the tree is well-formed (rules 1 to 3 above).
//! * **Pre**: what must be true when the function is called. The caller is responsible for it.
//! * **Post**: what is true when the function returns, if Pre held.
//!
//! The allocator starts as empty slices (no words at all), which is trivially WF, so WF holds from the start.
//!
//! # How the code keeps the tree well-formed
//!
//! Only two functions write to the tree, and each writes to one part only:
//!
//! * [`BitmapAllocator::set_range`] is the only function that writes level 0. It may break rule 3 above the words
//!   it touched. Before it returns, it asks `sync_up` to fix that.
//! * [`BitmapAllocator::sync_up`] is the only function that writes level 1 and above. It restores rule 3.
//!
//! Everything else (`is_range_free`, `search`, `alloc`, `dealloc`) only reads the tree or calls these two functions.
//! So well-formedness is lost only inside `set_range`, for a short time, and regained before it returns.

use super::locked::Locked;
use crate::core::memory_layout::ConfidentialMemoryAddress;
use crate::error::Error;
use alloc::alloc::{GlobalAlloc, Layout};
use core::ptr;
use pointers_utility::ptr_byte_add_mut;

pub const MIN_ALLOC_SIZE: usize = 16;
pub const NUM_LEVELS: usize = 5; // L0 (16B), L1 (1KiB), L2 (64KiB), L3 (4MiB), L4 (256MiB)

/// Returns a word that has `count` ones in a row, starting at bit `shift`.
///
/// # Pre
/// * `count <= 64`.
/// * If `count < 64`, then `count + shift <= 64`. If `count == 64`, then `shift == 0`.
///
/// # Post
/// * Bit `i` of the result is 1 if and only if `shift <= i < shift + count`.
/// * Nothing else is read or changed.
fn bit_mask(count: usize, shift: usize) -> usize {
    if count >= usize::BITS as usize { !0usize } else { ((1usize << count) - 1) << shift }
}

/// Number of leaf blocks covered by a single bit on `level`.
///
/// # Pre
/// * `level < NUM_LEVELS`.
///
/// # Post
/// * The result is `64^level`.
/// * Nothing else is read or changed.
fn blocks_per_bit(level: usize) -> usize {
    1usize << (6 * level)
}

/// Decides where to look for a request: returns `(level, bits)`.
///
/// The request is rounded up to a power-of-two number of blocks. The answer says "take `bits` neighbouring bits on
/// `level`". If a request needs more than 32 bits on one level, it moves one level up and uses fewer, bigger bits.
/// This keeps the waste below 2x.
///
/// # Pre
/// * The request is not bigger than what the top level can describe: `max(size, align)` is at most
///   `64 * blocks_per_bit(NUM_LEVELS - 1) * MIN_ALLOC_SIZE` bytes.
///
/// # Post
/// * `level < NUM_LEVELS`, and `bits` is a power of two with `1 <= bits <= 64`.
/// * The group has `bits * blocks_per_bit(level)` blocks. That is at least `max(size, align, MIN_ALLOC_SIZE)`
///   bytes, and less than twice that size rounded up to a whole number of blocks.
/// * The answer depends only on `layout`. So `alloc` and `dealloc`, given the same layout, agree on the group size.
/// * Nothing else is read or changed.
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

/// Looks for `bits` ones in a row inside `word`, where the run must start at a multiple of `bits`.
///
/// # Pre
/// * `bits` is a power of two with `1 <= bits <= 64`.
///
/// # Post
/// * If the result is `Some(p)`: `p % bits == 0`, `p + bits <= 64`, bits `p .. p + bits` of `word` are all 1, and
///   `p` is the lowest position with this property.
/// * If the result is `None`: no such run exists in `word`.
/// * Nothing else is read or changed.
fn find_aligned_bits(word: usize, bits: usize) -> Option<usize> {
    let mask = bit_mask(bits, 0);
    (0..usize::BITS as usize).step_by(bits).find(|&pos| (word >> pos) & mask == mask)
}

/// Returns the bits of leaf word `w` that belong to the block range `[first, first + count)`.
///
/// # Pre
/// * `count > 0`, and `first + count` does not overflow.
/// * `w` is one of the words returned by `leaf_words(first, count)`.
///
/// # Post
/// * Bit `i` of the result is 1 if and only if block `64 * w + i` is in the range.
/// * Nothing else is read or changed.
fn leaf_mask(first: usize, count: usize, w: usize) -> usize {
    let word_start = w * 64;
    let lo = first.max(word_start) - word_start;
    let hi = (first + count).min(word_start + 64) - word_start;
    bit_mask(hi - lo, lo)
}

/// Returns the indexes of the leaf words that the block range `[first, first + count)` touches.
///
/// # Pre
/// * `count > 0`, and `first + count` does not overflow.
///
/// # Post
/// * The result is the words `first / 64` up to (not including) `ceil((first + count) / 64)`.
/// * A word is in the result if and only if it holds at least one block of the range.
/// * Nothing else is read or changed.
fn leaf_words(first: usize, count: usize) -> core::ops::Range<usize> {
    first / 64..(first + count + 63) / 64
}

/// A 64-way multi-level bitmap heap allocator.
///
/// # Invariant
/// * `levels` is WF (see the module description). Every function below expects this when it is called and
///   gives it back when it returns. The only exception is the short time inside `set_range`.
/// * `data_start` is 0 until `init` succeeds. After that, it is the address of block 0.
/// * The bitmaps themselves live at the start of the heap, before `data_start`. They are not part of any block.
pub struct BitmapAllocator {
    data_start: usize,
    levels: [&'static mut [usize]; NUM_LEVELS],
}

impl BitmapAllocator {
    pub const fn new() -> Self {
        Self { data_start: 0, levels: [&mut [], &mut [], &mut [], &mut [], &mut []] }
    }

    /// Sets up the allocator on the memory `[start_address, end_address)`.
    ///
    /// It reserves room for the bitmaps at the start of the memory, cuts that room into the levels, and marks
    /// every real block as free.
    ///
    /// # Pre
    /// * `[start_address, end_address)` is memory that this allocator may write, and nobody else uses it.
    /// * `start_address` is aligned for `usize`, and `start_address <= end_address`.
    /// * `init` has not succeeded before on this allocator.
    ///
    /// # Post
    /// * On `Ok`: the tree is WF, and the free set is exactly all real blocks `0 .. N`. Here `N` is the memory left
    ///   after the bitmaps, divided by `MIN_ALLOC_SIZE`. `data_start` is the address of block 0, so it is not 0.
    /// * On `Err`: nothing was written, and the allocator is as before (`data_start == 0`). The error is
    ///   `NotEnoughMemory` if the bitmaps do not fit, or `InvalidMemoryBoundary` if the address arithmetic fails.
    ///
    /// # Why WF holds
    /// It starts from an all-zero tree. That is WF: nothing is free, and every bit, leaf or summary, says "nothing
    /// free". Then it calls `set_range` to free the real blocks, and `set_range` keeps the tree WF.
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

        // Free every real block. The tree was all zeros (well-formed); `set_range` keeps it well-formed.
        self.set_range(0, (heap_size - meta_bytes) / MIN_ALLOC_SIZE, true);

        self.data_start = data_start_ptr.addr();
        Ok(())
    }

    /// Repairs the summary bits on the path from leaf word `leaf_word` up to the root.
    ///
    /// Going upwards, level by level, it sets the bit that stands for the current word in its parent to "the
    /// current word is not zero". It does this always, without checking whether the bit already had that value.
    /// This is the only function that writes level 1 and above.
    ///
    /// # Pre
    /// * `leaf_word < levels[0].len()`.
    /// * The tree is WF, except that summary bits on the path above `leaf_word` may be out of date. This happens
    ///   right after the leaf word was changed. (Rule 3 may fail only for the bits on this path.)
    ///
    /// # Post
    /// * The tree is WF.
    /// * Level 0 is unchanged. Only summary bits on the path were written, so the free set is unchanged.
    ///
    /// # Why WF holds
    /// Only the bits on this path can be out of date. The loop fixes them from the bottom up. Fixing a bit can
    /// change its word, which makes the bit above it out of date, but that bit is the next step of the loop.
    /// When the loop reaches the root, every bit on the path matches its child word. Bits outside the path were
    /// right before, and their child words did not change, so they are still right.
    fn sync_up(&mut self, leaf_word: usize) {
        let mut idx = leaf_word;
        for lvl in 0..NUM_LEVELS - 1 {
            let bit = 1usize << (idx % 64);
            let child_is_non_empty = self.levels[lvl][idx] != 0;
            let parent = &mut self.levels[lvl + 1][idx / 64];
            if child_is_non_empty {
                *parent |= bit;
            } else {
                *parent &= !bit;
            }
            idx /= 64;
        }
    }

    /// Marks the blocks `[first, first + count)` as free (`free == true`) or taken (`free == false`).
    ///
    /// For every leaf word that the range touches, it sets or clears the right leaf bits, then calls `sync_up`
    /// for that word. This is the only function that writes level 0.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `count > 0`.
    /// * The range lies inside the real blocks: `first + count <= N`. (Otherwise it would write into the padding
    ///   bits, which must stay 0.)
    ///
    /// # Post
    /// * The tree is WF.
    /// * The free set changed only inside the range. If `free`, the free set is the old one plus the range. If
    ///   not `free`, it is the old one minus the range.
    /// * The function does not look at the old state of the blocks. Freeing a free block or taking a taken block
    ///   changes nothing. Whether that makes sense is for the caller to decide.
    ///
    /// # Why WF holds
    /// After each word, `sync_up` has made the tree WF again. So the tree is not WF only between writing a leaf
    /// word and calling `sync_up` for it.
    fn set_range(&mut self, first: usize, count: usize, free: bool) {
        for w in leaf_words(first, count) {
            let mask = leaf_mask(first, count, w);
            if free {
                self.levels[0][w] |= mask;
            } else {
                self.levels[0][w] &= !mask;
            }
            self.sync_up(w);
        }
    }

    /// Tells whether every block in `[first, first + count)` is a real block and is free.
    ///
    /// It reads the leaf words that the range touches and checks that all the needed bits are 1.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `count > 0`, and `first + count` does not overflow.
    ///
    /// # Post
    /// * The tree is unchanged.
    /// * The result is `true` if and only if the whole range is inside the free set. A range that sticks out past
    ///   the real blocks gives `false`, because padding bits are 0 (and words that do not exist count as not free).
    ///
    /// # Why it only looks at leaves
    /// The leaves are the truth about what is free. The upper levels only say where it is worth looking.
    fn is_range_free(&self, first: usize, count: usize) -> bool {
        let words = leaf_words(first, count);
        words.end <= self.levels[0].len() && words.into_iter().all(|w| self.levels[0][w] & leaf_mask(first, count, w) == leaf_mask(first, count, w))
    }

    /// Looks for a free, aligned group of `bits` neighbouring bits on level `target`, somewhere below the word
    /// `(level, idx)`, and takes it. Returns the number of the first block of the group, or `None`.
    ///
    /// Above `target`, it tries every set bit, lowest first, and goes into that child. A set bit only promises that
    /// *something* is free below it. On `target`, it picks runs of `bits` set bits that start at a multiple of
    /// `bits`, then asks `is_range_free` whether the whole group is really free. If yes, it takes the group with
    /// `set_range`. If no, it tries the next candidate.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `(level, idx)` is an existing word: `level < NUM_LEVELS` and `idx < levels[level].len()`.
    /// * `target <= level`, and `bits` is a power of two with `1 <= bits <= 64`.
    ///
    /// # Post
    /// * The tree is WF.
    /// * If the result is `Some(first)`:
    ///   - the group is the `bits * blocks_per_bit(target)` blocks starting at `first`;
    ///   - the group was entirely free before and is entirely taken now. The rest of the free set is unchanged;
    ///   - the group lies below `(level, idx)`, and `first` is a multiple of the group size.
    /// * If the result is `None`: nothing was changed, and no group of this size and alignment below `(level, idx)`
    ///   is free. The search never skips a bit that could lead to such a group, because a zero bit has no free
    ///   block below it (rule 3).
    ///
    /// # Why WF holds
    /// Only `set_range` changes the tree, so WF is kept. A wrong hint can only waste time, never give a wrong
    /// answer, because `is_range_free` checks the leaves before anything is taken.
    fn search(&mut self, level: usize, idx: usize, target: usize, bits: usize) -> Option<usize> {
        let step = if level == target { bits } else { 1 };
        let mut word = self.levels[level][idx];
        while let Some(pos) = find_aligned_bits(word, step) {
            let bit_index = idx * 64 + pos;
            if level == target {
                let (first, count) = (bit_index * blocks_per_bit(level), bits * blocks_per_bit(level));
                if self.is_range_free(first, count) {
                    self.set_range(first, count, false);
                    return Some(first);
                }
            } else if let Some(first) = self.search(level - 1, bit_index, target, bits) {
                return Some(first);
            }
            word &= !bit_mask(step, pos);
        }
        None
    }

    /// Allocates memory for `layout`. Returns null if there is no room.
    ///
    /// It turns the layout into "how many bits on which level" (`allocation_target`), then asks every root word
    /// in turn to find and take a free group (`search`).
    ///
    /// # Pre
    /// * The tree is WF.
    /// * The layout is within what `allocation_target` accepts.
    ///
    /// # Post
    /// * The tree is WF.
    /// * On success (the pointer is not null):
    ///   - the pointer is the address of block `first`, that is `data_start + first * MIN_ALLOC_SIZE`;
    ///   - the group of blocks starting there has at least `layout.size()` bytes and was entirely free before. It is
    ///     taken now, so it does not overlap any other allocation that is still alive;
    ///   - the offset of the pointer from `data_start` is a multiple of the group size, so it is aligned to
    ///     `layout.align()` relative to `data_start`.
    /// * On failure (null pointer): the tree is unchanged. This also happens if `init` has not succeeded yet.
    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        if self.data_start == 0 {
            return ptr::null_mut();
        }
        let (target, bits) = allocation_target(layout);
        let root = NUM_LEVELS - 1;
        for node in 0..self.levels[root].len() {
            if let Some(first) = self.search(root, node, target, bits) {
                return ptr::without_provenance_mut(self.data_start + first * MIN_ALLOC_SIZE);
            }
        }
        ptr::null_mut()
    }

    /// Gives back memory that `alloc` returned.
    ///
    /// It works out the same group of blocks that `alloc` took (the same `layout` gives the same answer from
    /// `allocation_target`) and marks it free with `set_range`.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `ptr` was returned by `alloc` with this same `layout`, and it has not been freed since. The function does
    ///   not check this. If it is not true, the function may free blocks that belong to somebody else.
    ///
    /// # Post
    /// * The tree is WF.
    /// * The group of blocks of the allocation was added to the free set. The rest of the free set is unchanged.
    /// * If `ptr` is null, or `init` has not succeeded yet, nothing is changed.
    /// * Neighbouring free blocks are merged without extra work: once all leaf bits below a higher-level bit are
    ///   1, a later `search` on that level sees the whole group as one free block. There is no separate merge step.
    pub fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        if ptr.is_null() || self.data_start == 0 {
            return;
        }
        let (target, bits) = allocation_target(layout);
        let first = ptr.addr().saturating_sub(self.data_start) / MIN_ALLOC_SIZE;
        self.set_range(first, bits * blocks_per_bit(target), true);
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
