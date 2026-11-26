// SPDX-FileCopyrightText: 2026 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

//! A heap allocator that tracks free memory with a tree of bitmaps. Every word above the leaves has one SOME bit per child, and a summary
//! (`fits`) of which allocation sizes can be served below it. The summary makes the search for free memory take a bounded number of steps.
//!
//! # The picture
//!
//! The heap is cut into small *blocks* of `MIN_ALLOC_SIZE` bytes. The tree has `NUM_LEVELS` levels.
//!
//! * Level 0 (the *leaves*) has one bit per block. Bit = 1 means "this block is free". A leaf word is one `usize`.
//! * On level 1 and above, a word is a `BitmapTreeNode` of two `usize` words. Its `some` word has one **SOME** bit for every word of the
//!   level below (its *child*). The SOME bit is 1 if the child has at least one free block somewhere below it. Its `fits` word is a summary
//!   of what can be allocated below the node (rule 5).
//! * So one bit on level `l` covers `64^l` blocks.
//!
//! For a child word `c` we write `some(c)` for "`c` has a free block below it" and `all(c)` for "all blocks below `c` are free (and are
//! real blocks)". For a leaf word, `some(c)` is "`c != 0`" and `all(c)` is "`c == !0`". For a node, `some(c)` is "its `some` word is not
//! 0", and `all(c)` is "the bit of its `fits` that stands for 64 neighbouring bits on its own level is 1" (see rule 5).
//!
//! # Taking a big group without touching what is below it
//!
//! To take a group of blocks that is big (say 4 MiB), the allocator only clears the SOME bits that stand for the group. It does **not**
//! change the words below them. They stay as they were, and they were entirely free: leaf words are all-ones, nodes have all SOME bits set
//! and the `fits` of an entirely free node. We say such words are *asleep*: they look free, but nobody reads them, because the bit above
//! says "nothing is free here". When the group is given back, the same bits are set again, and the words below are awake and correct again.
//! So taking or giving back a group of any size costs a few word writes, not one write per leaf word.
//!
//! # Well-formed tree (WF)
//!
//! The tree is *well-formed* when all of the following hold. Every rule is about one SOME bit and its child `c`, or about one node.
//!
//! 1. **Shape.** Level `l+1` has one SOME bit for every word of level `l`, so it has `ceil(words(l) / 64)` words.
//! 2. **Padding is empty.** Leaf bits that are not real blocks are 0. A SOME bit whose child does not exist is 0.
//! 3. **A set SOME bit tells the truth.** If SOME = 1, then `some(c)`.
//! 4. **A clear SOME bit hides the child.** If SOME = 0, then `c` is either empty (`not some(c)`) or asleep (`all(c)`).
//! 5. **FITS is exact.** Every node `w` stores `fits(w)`, with one bit for every target `(t, k)`, `t <= level(w)`, `0 <= k < 7` (bit number
//!    `t * 7 + k`). The bit is 1 if and only if, below `w`, there are `2^k` neighbouring bits on level `t`, starting at a multiple of
//!    `2^k`, that are all entirely free. For `t == level(w)` these are bits of `w` whose child `c` has SOME = 1 and `all(c)`. For `t <
//!    level(w)` it is the case if some child `c` of `w` with SOME = 1 has the bit set in `fits(c)`. On level 0 nothing is stored: `fits` of
//!    a leaf word is computed from the word. A node that is entirely free has all its bits set, and so does an asleep node, because it was
//!    entirely free when it was taken and nobody writes there. So it is right again when it wakes up.
//!
//! A block is **free** if its leaf bit is 1 and every SOME bit on its path up to the root is 1. This is the
//! *free set*. Blocks below a clear SOME bit are never free, whatever the words below them say.
//!
//! # Words used in the contracts
//!
//! * **Real block**: a block that is part of the heap. There are `N` of them, numbered `0 .. N`.
//! * **Word** `(level, idx)`: word number `idx` on `level`. On level 0 it is the leaf word `leaves[idx]`. On a higher level it is the
//!   `BitmapTreeNode` `nodes[level - 1][idx]`: its `some` word holds 64 SOME bits, one for each child, and its `fits` word is the summary
//!   of rule 5.
//! * **Neighbouring bits** `(level, idx, first_bit, count)`: the bits `first_bit .. first_bit + count` of word `(level, idx)`. One
//!   allocation is made of such bits, and they stand for `count * blocks_per_bit(level)` neighbouring blocks, starting at block `(64 * idx
//!   + first_bit) * blocks_per_bit(level)`.
//! * **Entirely free bit**: a bit of word `(level, idx)` that stands for blocks that are all free. On level 0 it is a leaf bit that is 1.
//!   On a higher level it is a bit whose child `c` has SOME = 1 and `all(c)`.
//! * **Allocation target** `AllocationTarget { level, bits }`: what a request needs. It is `bits` neighbouring bits on `level`.
//! * **Asleep word**: a word below a clear SOME bit that was left as it was when a group was taken.
//! * **Pre**: what must be true when the function is called. The caller is responsible for it.
//! * **Post**: what is true when the function returns, if Pre held.
//!
//! # How the code keeps the tree well-formed
//!
//! * [`BitmapAllocator::write_masked_bits`] is the only function that writes leaf words and SOME bits. It can break rules 3 and 4 only for
//!   the one SOME bit above the word, and rule 5 for the word and the words above it.
//! * [`BitmapAllocator::update_ancestors`] is the only function that writes `fits`. Going up from a given word, one level after the other,
//!   it sets the SOME bit that stands for the word, and recomputes `fits` of the word above, so that both describe the word as it is now.
//!   It restores WF.
//! * [`BitmapAllocator::mark_neighbouring_bits`] is the only function that changes the free set. It calls `write_masked_bits` once and then
//!   `update_ancestors`.
//! * Everything else (`find_and_take`, `alloc`, `dealloc`) reads the tree, or calls `mark_neighbouring_bits` once.
//!
//! So the tree is not WF only inside `mark_neighbouring_bits`, between its `write_masked_bits` and the end of its `update_ancestors`.
//!
//! # Cost
//!
//! `fits` is exact, so the search never enters a part of the tree that cannot serve the request, and it never goes back. A search reads
//! at most 64 words per level, and every change recomputes at most one word per level from at most 64 words. So `alloc` and `dealloc` both
//! need at most about `64 * NUM_LEVELS` word reads, however big the heap is and however fragmented it is.

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
/// * `1 <= count <= 64` and `count + shift <= 64`.
///
/// # Post
/// * Bit `i` of the result is 1 if and only if `shift <= i < shift + count`.
/// * Nothing else is read or changed.
fn bit_mask(count: usize, shift: usize) -> usize {
    (usize::MAX >> (usize::BITS as usize - count)) << shift
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

/// Finds all places in `word` where `bits` ones in a row start, and the first of them is at a multiple of `bits`.
///
/// It folds the word with itself with shifts `1, 2, 4, .., bits / 2`, so that bit `i` of the result says that bits `i .. i + bits` of
/// `word` are all 1 (the shifts bring in zeros, so a run never crosses the top of the word). Then it keeps the positions that are
/// multiples of `bits`.
///
/// # Pre
/// * `bits` is a power of two with `1 <= bits <= 64`.
///
/// # Post
/// * Bit `p` of the result is 1 if and only if `p % bits == 0`, `p + bits <= 64`, and bits `p .. p + bits` of `word` are all 1.
/// * Nothing else is read or changed.
fn aligned_run_starts(word: usize, bits: usize) -> usize {
    let mut runs = word;
    let mut shift = 1;
    while shift < bits {
        runs &= runs >> shift;
        shift <<= 1;
    }
    // `MAX / (2^bits - 1)` has a one at every multiple of `bits` (and is 1 for `bits == 64`).
    runs & (usize::MAX / bit_mask(bits, 0))
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
    let starts = aligned_run_starts(word, bits);
    if starts == 0 { None } else { Some(starts.trailing_zeros() as usize) }
}

/// Number of run sizes `1, 2, 4, .., 64` that a `fits` summary distinguishes on one level.
const RUN_SIZES: usize = 7;

/// Index, inside the run sizes of one level, of the run of 64 bits: it stands for "all bits of the word".
const FULL_RUN: usize = RUN_SIZES - 1;

/// Tells which aligned runs of ones exist in `word`: bit `k` of the result is 1 if and only if `find_aligned_bits(word, 1 << k)` is
/// `Some`, for `k < RUN_SIZES`. Bits `RUN_SIZES` and above are 0.
///
/// # Post
/// * Nothing else is read or changed.
fn run_summary(word: usize) -> usize {
    let mut summary = 0;
    for k in 0..RUN_SIZES {
        if aligned_run_starts(word, 1usize << k) != 0 {
            summary |= 1usize << k;
        }
    }
    summary
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
    /// * The group has `bits * blocks_per_bit(level)` blocks. That is at least `max(size, align, MIN_ALLOC_SIZE)` bytes, and less than
    ///   twice that size rounded up to a whole number of blocks.
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

    /// The bit of a `fits` summary that stands for this target: bit `level * RUN_SIZES + log2(bits)`.
    fn fits_bit(self) -> usize {
        1usize << (self.level * RUN_SIZES + self.bits.trailing_zeros() as usize)
    }
}

/// One word of the tree on level 1 or above: 64 SOME bits (`some`) and the summary of what fits below it (`fits`, rule 5).
#[repr(C)]
struct BitmapTreeNode {
    some: usize,
    fits: usize,
}

/// Number of `usize` words in a `BitmapTreeNode`.
const NODE_WORDS: usize = core::mem::size_of::<BitmapTreeNode>() / core::mem::size_of::<usize>();

/// A 64-way multi-level bitmap heap allocator.
///
/// # Invariant
/// * The tree is WF (see the module description). Every function below expects this when it is called and gives it back when it returns.
///   The only exception is the short time inside `mark_neighbouring_bits`.
/// * `leaves` is the leaf bitmap (level 0). For `l >= 1`, `nodes[l - 1]` holds the words of level `l`. Leaves have no `BitmapTreeNode`: a
///   leaf bit is free or not, and `fits` of a leaf word is computed from the word.
/// * `data_start` is 0 until `init` succeeds. After that, it is the address of block 0.
/// * The bitmaps themselves live at the start of the heap, before `data_start`. They are not part of any block.
pub struct BitmapAllocator {
    data_start: usize,
    leaves: &'static mut [usize],
    nodes: [&'static mut [BitmapTreeNode]; NUM_LEVELS - 1],
}

impl BitmapAllocator {
    pub const fn new() -> Self {
        Self { data_start: 0, leaves: &mut [], nodes: [&mut [], &mut [], &mut [], &mut []] }
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

        // Calculate metadata requirements and slice partitions. Levels 1.. have a `BitmapTreeNode` (`NODE_WORDS` words) per word, level 0
        // has one word.
        let max_blocks = heap_size / MIN_ALLOC_SIZE;
        let mut level_lens = [0usize; NUM_LEVELS];
        let mut active = max_blocks;
        let mut total_words = 0;
        for lvl in 0..NUM_LEVELS {
            level_lens[lvl] = (active + 63) / 64;
            total_words += if lvl == 0 { level_lens[lvl] } else { NODE_WORDS * level_lens[lvl] };
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

        let (leaves, mut rest) = meta_slice.split_at_mut(level_lens[0]);
        self.leaves = leaves;
        for lvl in 1..NUM_LEVELS {
            let (slice, remaining) = rest.split_at_mut(NODE_WORDS * level_lens[lvl]);
            // SAFETY: `BitmapTreeNode` is `repr(C)` with `NODE_WORDS` `usize` fields, so it has the size and alignment of `NODE_WORDS`
            // words, and the all-zero words (written above) are a valid node.
            self.nodes[lvl - 1] = unsafe { core::slice::from_raw_parts_mut(slice.as_mut_ptr() as *mut BitmapTreeNode, level_lens[lvl]) };
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
    /// * `level < NUM_LEVELS` and `idx < words(level)`.
    fn read_some_bits(&self, level: usize, idx: usize) -> usize {
        if level == 0 { self.leaves[idx] } else { self.nodes[level - 1][idx].some }
    }

    /// The `fits` summary of word `(level, idx)`. On level 0 it is not stored, it is computed from the leaf word (`run_summary`).
    ///
    /// # Pre
    /// * `level < NUM_LEVELS` and `idx < words(level)`.
    fn read_fits(&self, level: usize, idx: usize) -> usize {
        if level == 0 { run_summary(self.leaves[idx]) } else { self.nodes[level - 1][idx].fits }
    }

    /// Reads the children of node `(level, idx)` that have SOME = 1, and returns `(fits, free)`:
    /// * `fits` is the OR of the `fits` of these children. It tells which targets below the node fit inside a child.
    /// * `free` has bit `b` set if and only if child `b` has SOME = 1 and `all(c)`, that is, `b` is an entirely free bit of the node. A
    ///   child is `all(c)` if the bit of its `fits` for the run of 64 bits on its own level is set.
    ///
    /// It reads at most 64 words.
    ///
    /// # Pre
    /// * `1 <= level < NUM_LEVELS` and `idx < words(level)`.
    /// * The `fits` of the children with SOME = 1 are right (rule 5).
    ///
    /// # Post
    /// * Nothing is changed.
    fn scan_children(&self, level: usize, idx: usize) -> (usize, usize) {
        let full_run_bit = 1usize << ((level - 1) * RUN_SIZES + FULL_RUN);
        let mut fits = 0;
        let mut free = 0;
        let mut some_bits = self.read_some_bits(level, idx);
        while some_bits != 0 {
            let bit = some_bits.trailing_zeros() as usize;
            some_bits &= some_bits - 1;
            let child_fits = self.read_fits(level - 1, 64 * idx + bit);
            fits |= child_fits;
            if child_fits & full_run_bit != 0 {
                free |= 1usize << bit;
            }
        }
        (fits, free)
    }

    /// Writes the bits that are 1 in `mask` of word `(level, idx)`: they become 1 if `set`, and 0 if not. This is the only function that
    /// writes leaf words and SOME bits.
    ///
    /// # Pre
    /// * `level < NUM_LEVELS` and `idx < words(level)`.
    ///
    /// # Post
    /// * The bits of the word in `mask` have the new value. Everything else is unchanged.
    /// * The tree may be not WF: rules 3 and 4 may fail for the one SOME bit above this word, and rule 5 may fail for this word and the
    ///   words above it. No other rule and no other bit is affected.
    fn write_masked_bits(&mut self, level: usize, idx: usize, mask: usize, set: bool) {
        let word = if level == 0 { &mut self.leaves[idx] } else { &mut self.nodes[level - 1][idx].some };
        if set {
            *word |= mask;
        } else {
            *word &= !mask;
        }
    }

    /// Repairs the tree above word `(level, idx)`, which was just changed. Going up, one level at a time, it recomputes the `fits` of the
    /// current word if it is a node, and then sets the SOME bit that stands for the current word in its parent to the truth: SOME = "the
    /// word has something free". It does this always, without checking what the bit was.
    ///
    /// It reads and writes nothing below `(level, idx)`, except that it reads the up to 64 children of each node on the path.
    ///
    /// # Pre
    /// * `level < NUM_LEVELS` and `idx < words(level)`.
    /// * The tree is WF, except that rules 3, 4 and 5 may fail for the words and SOME bits on the path starting at `(level, idx)`. This
    ///   happens right after the word was changed.
    /// * The word `(level, idx)` is not asleep. (Then no word above it is asleep either.)
    ///
    /// # Post
    /// * The tree is WF.
    /// * Only the `fits` of nodes on the path starting at `(level, idx)`, and the SOME bits above `(level, idx)` on that path, were
    ///   written.
    ///
    /// # Why WF holds
    /// Only the words and SOME bits on this path can be wrong. The loop fixes them from the bottom up. Fixing a word changes it, which may
    /// make the SOME bit and the `fits` above it wrong, but they are the next step of the loop. The SOME bit written is the truth, so rules
    /// 3 and 4 hold for it: a set bit goes with a word that has something free, and a clear bit goes with an empty word. Rule 5 holds
    /// because `scan_children` is the definition of rule 5, and it is evaluated after the SOME bits and the `fits` of the children were
    /// fixed. Words off the path are still right, because their children did not change.
    fn update_ancestors(&mut self, mut level: usize, mut idx: usize) {
        loop {
            if level > 0 {
                let (child_fits, free) = self.scan_children(level, idx);
                self.nodes[level - 1][idx].fits = child_fits | (run_summary(free) << (level * RUN_SIZES));
            }
            if level + 1 == NUM_LEVELS {
                return;
            }
            let has_free_block = self.read_some_bits(level, idx) != 0;
            self.write_masked_bits(level + 1, idx / 64, 1usize << (idx % 64), has_free_block);
            level += 1;
            idx /= 64;
        }
    }

    /// Takes (`mark_as_free == false`) or gives back (`mark_as_free == true`) the neighbouring bits `first_bit .. first_bit + count` of
    /// word `(level, idx)`. Together they stand for one allocation.
    ///
    /// It writes these bits (the leaf bits on level 0, SOME bits above), then updates the tree above them. Nothing below them is written,
    /// whatever their size. This is the only function that changes the free set.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `level < NUM_LEVELS`, `idx < words(level)`, `1 <= count`, `first_bit + count <= 64`.
    /// * Every one of the bits points to a real block (or to a child that exists).
    /// * The word `(level, idx)` is not asleep.
    /// * If `mark_as_free == false`: the bits are entirely free.
    /// * If `mark_as_free == true`: the bits are taken. Every child below them (if any) is entirely free, because it was entirely free when
    ///   the bits were taken, and nobody writes there while they are taken. On level 0 there is no child, so there is nothing to require.
    ///
    /// # Post
    /// * The tree is WF.
    /// * The free set changed only by the blocks that these bits stand for: they are free now if `mark_as_free`, taken if not. The rest of
    ///   the free set is unchanged.
    /// * At most `2 * NUM_LEVELS` words were written, because only the word `(level, idx)` and the words above it are written.
    ///
    /// # Why WF holds
    /// * Taking: the children below the bits are entirely free, which rule 4 allows below a clear SOME bit.
    /// * Giving back: the children below the bits are entirely free, so they have SOME = 1 and `all(c)`, which rule 3 allows below a set
    ///   SOME bit.
    /// * Either way, `write_masked_bits` can make wrong only the SOME bit and the `fits` above the word, and `update_ancestors` repairs
    ///   them.
    fn mark_neighbouring_bits(&mut self, level: usize, idx: usize, first_bit: usize, count: usize, mark_as_free: bool) {
        self.write_masked_bits(level, idx, bit_mask(count, first_bit), mark_as_free);
        self.update_ancestors(level, idx);
    }

    /// Looks for neighbouring bits of `target` that are free and aligned, somewhere below word `(level, idx)`, and takes them. Returns the
    /// number of the first block they stand for, or `None`.
    ///
    /// Above `target.level`, it goes into the first child that has SOME = 1 and whose `fits` has the bit of the target. The `fits` is
    /// exact (rule 5), so that child contains the allocation and the search never goes back. On `target.level`, it looks for `target.bits`
    /// neighbouring entirely free bits, starting at a multiple of `target.bits`, and takes them at once. It reads at most 64 words per
    /// level, so its cost is at most `64 * NUM_LEVELS` reads.
    ///
    /// # Pre
    /// * The tree is WF.
    /// * `(level, idx)` is an existing word that is not asleep: `level < NUM_LEVELS` and `idx < words(level)`, and every SOME bit on the
    ///   path above it is 1 (or it is a root word).
    /// * `target.level <= level`.
    ///
    /// # Post
    /// * The tree is WF.
    /// * If the result is `Some(first)`:
    ///   - the allocation is the `target.bits * blocks_per_bit(target.level)` blocks starting at `first`, below `(level, idx)`;
    ///   - these blocks were all free before and are all taken now. The rest of the free set is unchanged;
    ///   - `first` is a multiple of the allocation size, so the allocation is aligned to its own size.
    /// * The result is `None` if and only if the `fits` of `(level, idx)` does not have the bit of the target. Then nothing was changed,
    ///   and there is no aligned free allocation of this size below `(level, idx)`.
    ///
    /// # Why WF holds
    /// It only reads, except for one `mark_neighbouring_bits` on bits that are entirely free and not asleep. They are not asleep because
    /// the search reached them through set SOME bits only.
    fn find_and_take(&mut self, mut level: usize, mut idx: usize, target: AllocationTarget) -> Option<usize> {
        while level > target.level {
            let mut some_bits = self.read_some_bits(level, idx);
            idx = loop {
                if some_bits == 0 {
                    return None;
                }
                let child = 64 * idx + some_bits.trailing_zeros() as usize;
                some_bits &= some_bits - 1;
                if self.read_fits(level - 1, child) & target.fits_bit() != 0 {
                    break child;
                }
            };
            level -= 1;
        }
        let free_bits = if level == 0 { self.leaves[idx] } else { self.scan_children(level, idx).1 };
        let first_bit = find_aligned_bits(free_bits, target.bits)?;
        self.mark_neighbouring_bits(level, idx, first_bit, target.bits, false);
        Some((64 * idx + first_bit) * blocks_per_bit(level))
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
        for idx in 0..self.nodes[root - 1].len() {
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
    /// * Neighbouring free blocks are merged without extra work: `update_ancestors` recomputes the `fits` above a word, so as soon as the
    ///   word is entirely free, a later `find_and_take` on a higher level sees the whole group as free.
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
