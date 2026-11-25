// SPDX-FileCopyrightText: 2026 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

//! A heap allocator that tracks free memory with a tree of bitmaps. Every bit above the leaves comes as a pair.
//!
//! # The picture
//!
//! The heap is cut into small *blocks* of `MIN_ALLOC_SIZE` bytes. The tree has `NUM_LEVELS` levels.
//! Every node of the tree is one word of 64 bits.
//!
//! * Level 0 (the *leaves*) has one bit per block. Bit = 1 means "this block is free".
//! * On level 1 and above, one bit pair stands for one word of the level below (its *child*). The two bits of the pair are kept in two
//!   separate bitmaps, `some` and `all`:
//!   - the **SOME** bit is 1 if the child has at least one free block somewhere below it;
//!   - the **ALL** bit is 1 if every block below the child is free (and is a real block).
//! * So one bit on level `l` covers `64^l` blocks.
//!
//! For a child word `c` we write `some(c)` for "`c` has a free block below it" and `all(c)` for "all blocks below
//! `c` are free". Concretely, for a leaf word `some(c)` is "`c != 0`" and `all(c)` is "`c == !0`". For a word on
//! level 1 or above, `some(c)` is "its SOME bitmap is not 0" and `all(c)` is "its ALL bitmap is all ones".
//!
//! # Taking a big group without touching what is below it
//!
//! To take a group of blocks that is big (say 4 MiB), the allocator only clears the SOME and ALL bits that stand
//! for the group. It does **not** clear the words below them. They stay all-ones. We say such words are
//! *asleep*: they look free, but nobody reads them, because the bit above says "nothing is free here". When the
//! group is given back, the same bits are set again, and the words below are awake and correct again.
//! So taking or giving back a group of any size costs a few word writes, not one write per leaf word.
//!
//! # Well-formed tree (WF)
//!
//! The tree is *well-formed* when all of the following hold. Every rule is about one bit pair and its child `c`.
//!
//! 1. **Shape.** Level `l+1` has one bit pair for every word of level `l`, so each of its two bitmaps has `ceil(words(l) / 64)` words.
//! 2. **Padding is empty.** Leaf bits that are not real blocks are 0. A pair whose child does not exist is 0/0.
//! 3. **ALL implies SOME.** No pair has ALL = 1 and SOME = 0.
//! 4. **A set SOME bit tells the truth.** If SOME = 1, then `some(c)`, and ALL = 1 exactly when `all(c)`.
//! 5. **A clear SOME bit hides the child.** If SOME = 0, then ALL = 0, and `c` is either empty (`not some(c)`) or asleep (`all(c)`).
//!
//! A block is **free** if its leaf bit is 1 and every SOME bit on its path up to the root is 1. This is the
//! *free set*. Blocks below a clear SOME bit are never free, whatever the words below them say.
//! (Note: a word that is asleep is all ones in both bitmaps, so rules 3 and 4 hold inside it, too.)
//!
//! # Words used in the contracts
//!
//! * **Real block**: a block that is part of the heap. There are `N` of them, numbered `0 .. N`.
//! * **Word** `(level, idx)`: word number `idx` on `level`. On level 0 it is the leaf word `some[0][idx]`. On a higher level it is the two
//!   words `some[level][idx]` and `all[level][idx]`, which together hold 64 bit pairs, one for each child.
//! * **Neighbouring bits** `(level, idx, first_bit, count)`: the bits `first_bit .. first_bit + count` of word `(level, idx)`. One
//!   allocation is made of such bits, and they stand for `count * blocks_per_bit(level)` neighbouring blocks, starting at block `(64 * idx
//!   + first_bit) * blocks_per_bit(level)`.
//! * **Allocation target** `AllocationTarget { level, bits }`: what a request needs. It is `bits` neighbouring bits on `level`.
//! * **Asleep word**: a word below a clear SOME bit that was left all-ones when a group was taken.
//! * **Pre**: what must be true when the function is called. The caller is responsible for it.
//! * **Post**: what is true when the function returns, if Pre held.
//!
//! # How the code keeps the tree well-formed
//!
//! * [`BitmapAllocator::write_masked_bits`] is the only function that writes the tree. It writes some bits of one word, and can break rules
//!   4 and 5 only for the one pair above that word.
//! * [`BitmapAllocator::update_ancestor_pairs`] rewrites the pair of every word above a given word, one level after the other, so that each
//!   pair describes its child as it is now. It restores WF.
//! * [`BitmapAllocator::mark_neighbouring_bits`] is the only function that changes the free set. It calls `write_masked_bits` once and then
//!   `update_ancestor_pairs`.
//! * Everything else (`find_and_take`, `alloc`, `dealloc`) reads the tree, or calls `mark_neighbouring_bits` once.
//!
//! So the tree is not WF only inside `mark_neighbouring_bits`, between its `write_masked_bits` and the end of its `update_ancestor_pairs`.

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
    if count >= usize::BITS as usize {
        !0usize
    } else {
        ((1usize << count) - 1) << shift
    }
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

/// Looks for `bits` ones in a row inside `word`, where the first of them must be at a multiple of `bits`.
///
/// # Pre
/// * `bits` is a power of two with `1 <= bits <= 64`.
///
/// # Post
/// * If the result is `Some(p)`: `p % bits == 0`, `p + bits <= 64`, bits `p .. p + bits` of `word` are all 1, and `p` is the lowest
///   position with this property.
/// * If the result is `None`: no such bits exist in `word`.
/// * Nothing else is read or changed.
fn find_aligned_bits(word: usize, bits: usize) -> Option<usize> {
    let mask = bit_mask(bits, 0);
    (0..usize::BITS as usize).step_by(bits).find(|&pos| (word >> pos) & mask == mask)
}

/// Where to look for a request: `bits` neighbouring bits on `level`.
///
/// Invariant: `level < NUM_LEVELS` and `bits` is a power of two with `1 <= bits <= 64`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AllocationTarget {
    level: usize,
    bits: usize,
}

impl AllocationTarget {
    /// Decides where to look for a request.
    ///
    /// The request is rounded up to a power-of-two number of blocks. If a request needs more than 32 bits on one level, it moves one level
    /// up and uses fewer, bigger bits. This keeps the waste below 2x.
    ///
    /// # Pre
    /// * The request is not bigger than what the top level can describe: `max(size, align)` is at most `64 * blocks_per_bit(NUM_LEVELS - 1)
    ///   * MIN_ALLOC_SIZE` bytes.
    ///
    /// # Post
    /// * The invariant of `AllocationTarget` holds.
    /// * The group has `blocks()` blocks. That is at least `max(size, align, MIN_ALLOC_SIZE)` bytes, and less than twice that size rounded
    ///   up to a whole number of blocks.
    /// * The answer depends only on `layout`. So `alloc` and `dealloc`, given the same layout, agree on the group size.
    /// * Nothing else is read or changed.
    fn for_layout(layout: Layout) -> Self {
        let size = layout.size().max(layout.align()).max(MIN_ALLOC_SIZE);
        let total_blocks = (size + MIN_ALLOC_SIZE - 1) / MIN_ALLOC_SIZE;
        let mut blocks = total_blocks.next_power_of_two();
        let mut level = 0;
        while blocks > 32 && level + 1 < NUM_LEVELS {
            blocks = (blocks + 63) / 64;
            level += 1;
        }
        Self { level, bits: blocks.min(64) }
    }

    /// The number of blocks that the target stands for: `bits * blocks_per_bit(level)`.
    fn blocks(self) -> usize {
        self.bits * blocks_per_bit(self.level)
    }
}

/// A 64-way multi-level bitmap heap allocator.
///
/// # Invariant
/// * The tree is WF (see the module description). Every function below expects this when it is called and gives it back when it returns.
///   The only exception is the short time inside `mark_neighbouring_bits`.
/// * `some[0]` is the leaf bitmap. For `l >= 1`, `some[l]` and `all[l]` are the SOME and ALL bitmaps of level `l`. `all[0]` is empty and
///   not used, because a leaf bit is its own SOME and ALL bit.
/// * `data_start` is 0 until `init` succeeds. After that, it is the address of block 0.
/// * The bitmaps themselves live at the start of the heap, before `data_start`. They are not part of any block.
pub struct BitmapAllocator {
    data_start: usize,
    some: [&'static mut [usize]; NUM_LEVELS],
    all: [&'static mut [usize]; NUM_LEVELS],
}

impl BitmapAllocator {
    pub const fn new() -> Self {
        Self { data_start: 0, some: [&mut [], &mut [], &mut [], &mut [], &mut []], all: [&mut [], &mut [], &mut [], &mut [], &mut []] }
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
    /// * On `Ok`: the tree is WF, and the free set is exactly all real blocks `0 .. N`. Here `N` is the memory left after the bitmaps,
    ///   divided by `MIN_ALLOC_SIZE`. `data_start` is the address of block 0, so it is not 0.
    /// * On `Err`: nothing was written, and the allocator is as before (`data_start == 0`). The error is `NotEnoughMemory` if the bitmaps
    ///   do not fit, or `InvalidMemoryBoundary` if the address arithmetic fails.
    ///
    /// # Why WF holds
    /// It starts from an all-zero tree. That is WF: nothing is free, and every bit says "nothing free". Then it frees the real blocks with
    /// `mark_neighbouring_bits` on level 0, one leaf word at a time, and `mark_neighbouring_bits` keeps the tree WF.
    pub fn init(&mut self, start_address: ConfidentialMemoryAddress, end_address: ConfidentialMemoryAddress) -> Result<(), Error> {
        let heap_size = end_address.as_usize().saturating_sub(start_address.as_usize());
        debug!(
            "Initializing BitmapAllocator from 0x{:x} to 0x{:x} ({} bytes)",
            start_address.as_usize(),
            end_address.as_usize(),
            heap_size
        );

        // Calculate metadata requirements and slice partitions. Levels 1.. have two bitmaps, level 0 has one.
        let max_blocks = heap_size / MIN_ALLOC_SIZE;
        let mut level_lens = [0usize; NUM_LEVELS];
        let mut active = max_blocks;
        let mut total_words = 0;
        for lvl in 0..NUM_LEVELS {
            level_lens[lvl] = (active + 63) / 64;
            total_words += if lvl == 0 { level_lens[lvl] } else { 2 * level_lens[lvl] };
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
            self.some[lvl] = slice;
            rest = remaining;
        }
        for lvl in 1..NUM_LEVELS {
            let (slice, remaining) = rest.split_at_mut(level_lens[lvl]);
            self.all[lvl] = slice;
            rest = remaining;
        }

        // Free every real block, one leaf word at a time. The tree was all zeros (WF); `mark_neighbouring_bits` keeps it WF.
        let real_blocks = (heap_size - meta_bytes) / MIN_ALLOC_SIZE;
        for idx in 0..real_blocks.div_ceil(64) {
            self.mark_neighbouring_bits(0, idx, 0, (real_blocks - 64 * idx).min(64), true);
        }

        self.data_start = data_start_ptr.addr();
        Ok(())
    }

    /// The word of SOME bits of word `(level, idx)`. On level 0 it is the leaf word.
    ///
    /// # Pre
    /// * `level < NUM_LEVELS` and `idx < some[level].len()`.
    fn read_some_bits(&self, level: usize, idx: usize) -> usize {
        self.some[level][idx]
    }

    /// The word of ALL bits of word `(level, idx)`. On level 0 it is the leaf word too, because a leaf bit is its own ALL bit.
    ///
    /// # Pre
    /// * `level < NUM_LEVELS` and `idx < some[level].len()`.
    fn read_all_bits(&self, level: usize, idx: usize) -> usize {
        if level == 0 {
            self.some[0][idx]
        } else {
            self.all[level][idx]
        }
    }

    /// Writes the bits that are 1 in `mask` of word `(level, idx)`: the SOME bits become `some`, and the ALL bits become `all`. On level 0
    /// there is one bitmap only, and it gets `some`. This is the only function that writes the tree.
    ///
    /// # Pre
    /// * `level < NUM_LEVELS` and `idx < some[level].len()`.
    ///
    /// # Post
    /// * The bits of the word in `mask` have the new values. Everything else is unchanged.
    /// * The tree may be not WF: rules 4 and 5 may fail for the one pair above this word. No other rule and no other pair is affected.
    fn write_masked_bits(&mut self, level: usize, idx: usize, mask: usize, some: bool, all: bool) {
        if some {
            self.some[level][idx] |= mask;
        } else {
            self.some[level][idx] &= !mask;
        }
        if level > 0 {
            if all {
                self.all[level][idx] |= mask;
            } else {
                self.all[level][idx] &= !mask;
            }
        }
    }

    /// Rewrites the bit pair of every word above word `(level, idx)`, up to the root, so that each pair describes its child as it is now.
    ///
    /// Going upwards, one level at a time, it sets the pair that stands for the current word in its parent to the truth: SOME = "the word
    /// has something free", ALL = "the word is entirely free". It does this always, without checking what the pair was. It reads and
    /// writes nothing below `(level, idx)`.
    ///
    /// # Pre
    /// * `level < NUM_LEVELS` and `idx < some[level].len()`.
    /// * The tree is WF, except that rules 4 and 5 may fail for the pairs on the path above `(level, idx)`. This happens right after the
    ///   word was changed.
    /// * The word `(level, idx)` is not asleep. (Then no word above it is asleep either.)
    ///
    /// # Post
    /// * The tree is WF.
    /// * Only pairs on the path above `(level, idx)` were written.
    ///
    /// # Why WF holds
    /// Only the pairs on this path can be wrong. The loop fixes them from the bottom up. Fixing a pair changes its word, which may make the
    /// pair above it wrong, but that pair is the next step of the loop. The values it writes satisfy rules 3 to 5 by construction:
    /// `all(c)` implies `some(c)`, so ALL implies SOME; a set SOME bit goes with a word that has something free, and the ALL bit says if
    /// all of it is free; a clear SOME bit goes with an empty word. Pairs off the path are still right, because their children did not
    /// change.
    fn update_ancestor_pairs(&mut self, mut level: usize, mut idx: usize) {
        while level + 1 < NUM_LEVELS {
            let some = self.read_some_bits(level, idx) != 0;
            let all = self.read_all_bits(level, idx) == !0usize;
            self.write_masked_bits(level + 1, idx / 64, 1usize << (idx % 64), some, all);
            level += 1;
            idx /= 64;
        }
    }

    /// Takes (`mark_as_free == false`) or gives back (`mark_as_free == true`) the neighbouring bits `first_bit .. first_bit + count` of
    /// word `(level, idx)`. Together they stand for one allocation.
    ///
    /// It writes these bits (SOME and ALL, or the leaf bits on level 0), then updates the pairs above them. Nothing below them is written,
    /// whatever their size. This is the only function that changes the free set.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `level < NUM_LEVELS`, `idx < some[level].len()`, `1 <= count`, `first_bit + count <= 64`.
    /// * Every one of the bits points to a real block (or to a child that exists).
    /// * The word `(level, idx)` is not asleep.
    /// * If `mark_as_free == false`: the bits are entirely free. That means their ALL bits are 1 (on level 0: the leaf bits are 1). By rule
    ///   4, every child below them is then `all(c)`, so all-ones.
    /// * If `mark_as_free == true`: the bits are taken. Every child below them is all-ones (`all(c)`), because it was all-ones when they
    ///   were taken, and nobody writes there while they are taken. On level 0 there is no child, so there is nothing to require.
    ///
    /// # Post
    /// * The tree is WF.
    /// * The free set changed only by the blocks that these bits stand for: they are free now if `mark_as_free`, taken if not. The rest of
    ///   the free set is unchanged.
    /// * At most `2 * NUM_LEVELS` words were written, because only the word `(level, idx)` and the words above it are written.
    ///
    /// # Why WF holds
    /// * Taking: the children below the bits are all-ones, which rule 5 allows below a clear SOME bit.
    /// * Giving back: the children below the bits are all-ones, which rule 4 allows below a set SOME bit with ALL = 1, because they are
    ///   `some(c)` and `all(c)`.
    /// * Either way, `write_masked_bits` can make only the pair above the word wrong, and `update_ancestor_pairs` repairs it.
    fn mark_neighbouring_bits(&mut self, level: usize, idx: usize, first_bit: usize, count: usize, mark_as_free: bool) {
        self.write_masked_bits(level, idx, bit_mask(count, first_bit), mark_as_free, mark_as_free);
        self.update_ancestor_pairs(level, idx);
    }

    /// Looks for neighbouring bits of `target` that are free and aligned, somewhere below word `(level, idx)`, and takes them. Returns the
    /// number of the first block they stand for, or `None`.
    ///
    /// Above `target.level`, it tries every set SOME bit, lowest first, and goes into that child. A set SOME bit only promises that
    /// *something* is free below it, so the search may have to try the next bit. On `target.level`, it looks for `target.bits`
    /// neighbouring ALL bits that are all set, starting at a multiple of `target.bits`. An ALL bit is exact, so bits that are found are
    /// really free, and they are taken at once.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `(level, idx)` is an existing word that is not asleep: `level < NUM_LEVELS` and `idx < some[level].len()`, and every SOME bit on
    ///   the path above it is 1 (or it is a root word).
    /// * `target.level <= level`.
    ///
    /// # Post
    /// * The tree is WF.
    /// * If the result is `Some(first)`:
    ///   - the allocation is the `target.blocks()` blocks starting at `first`, below `(level, idx)`;
    ///   - these blocks were all free before and are all taken now. The rest of the free set is unchanged;
    ///   - `first` is a multiple of the allocation size, so the allocation is aligned to its own size.
    /// * If the result is `None`: nothing was changed, and there is no aligned free allocation of this size below `(level, idx)`. The
    ///   search skips only clear SOME bits (nothing is free below them, rule 5) and neighbouring ALL bits that are not all set (some block
    ///   below them is not free, rule 4).
    ///
    /// # Why WF holds
    /// It only reads, except for one `mark_neighbouring_bits` on bits that are entirely free and not asleep. They are not asleep because
    /// the search reached them through set SOME bits only.
    fn find_and_take(&mut self, level: usize, idx: usize, target: AllocationTarget) -> Option<usize> {
        if level == target.level {
            let first_bit = find_aligned_bits(self.read_all_bits(level, idx), target.bits)?;
            self.mark_neighbouring_bits(level, idx, first_bit, target.bits, false);
            return Some((64 * idx + first_bit) * blocks_per_bit(level));
        }
        let mut some_bits = self.read_some_bits(level, idx);
        while let Some(bit) = find_aligned_bits(some_bits, 1) {
            if let Some(first) = self.find_and_take(level - 1, 64 * idx + bit, target) {
                return Some(first);
            }
            some_bits &= !bit_mask(1, bit);
        }
        None
    }

    /// Allocates memory for `layout`. Returns null if there is no room.
    ///
    /// It turns the layout into an allocation target (`AllocationTarget::for_layout`), then asks every root word in turn to find and take
    /// free neighbouring bits (`find_and_take`).
    ///
    /// # Pre
    /// * The tree is WF.
    /// * The layout is within what `AllocationTarget::for_layout` accepts.
    ///
    /// # Post
    /// * The tree is WF.
    /// * On success (the pointer is not null):
    ///   - the pointer is the address of block `first`, that is `data_start + first * MIN_ALLOC_SIZE`;
    ///   - the group of blocks starting there has at least `layout.size()` bytes and was entirely free before. It is taken now, so it does
    ///     not overlap any other allocation that is still alive;
    ///   - the offset of the pointer from `data_start` is a multiple of the group size, so it is aligned to `layout.align()` relative to
    ///     `data_start`.
    /// * On failure (null pointer): the tree is unchanged. This also happens if `init` has not succeeded yet.
    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        if self.data_start == 0 {
            return ptr::null_mut();
        }
        let target = AllocationTarget::for_layout(layout);
        let root = NUM_LEVELS - 1;
        for idx in 0..self.some[root].len() {
            if let Some(first) = self.find_and_take(root, idx, target) {
                return ptr::without_provenance_mut(self.data_start + first * MIN_ALLOC_SIZE);
            }
        }
        ptr::null_mut()
    }

    /// Gives back memory that `alloc` returned.
    ///
    /// It works out the same neighbouring bits that `alloc` took (the same `layout` gives the same answer from
    /// `AllocationTarget::for_layout`) and gives them back with `mark_neighbouring_bits`.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `ptr` was returned by `alloc` with this same `layout`, and it has not been freed since. The function does not check this. If it is
    ///   not true, the function can corrupt the tree and free memory of somebody else.
    ///
    /// # Post
    /// * The tree is WF.
    /// * The blocks of the allocation were added to the free set. The rest of the free set is unchanged.
    /// * If `ptr` is null, or `init` has not succeeded yet, nothing is changed.
    /// * Neighbouring free blocks are merged without extra work: `update_ancestor_pairs` sets the ALL bit above a word as soon as the word
    ///   is entirely free, so a later `find_and_take` on a higher level sees the whole group as free.
    pub fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        if ptr.is_null() || self.data_start == 0 {
            return;
        }
        let target = AllocationTarget::for_layout(layout);
        let first_block = ptr.addr().saturating_sub(self.data_start) / MIN_ALLOC_SIZE;
        let bit = first_block / blocks_per_bit(target.level);
        self.mark_neighbouring_bits(target.level, bit / 64, bit % 64, target.bits, true);
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
