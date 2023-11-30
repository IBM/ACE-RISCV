// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![rr::import("ace.theories.page", "page_extra")]
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout, NonConfidentialMemoryAddress};
use crate::core::memory_protector::PageSize;
use crate::error::Error;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem;
use core::ops::Range;

pub trait PageState {}

pub struct UnAllocated {}
pub struct Allocated {}

impl PageState for UnAllocated {}
impl PageState for Allocated {}

#[derive(Debug)]
/// Specification:
/// Mathematically, we model a `Page` as a triple `(l, sz, v)`, where:
/// - `l` is the start address in memory,
/// - `sz` is the size of the page,
/// - and `v` is the sequence of bytes currently stored in the page.
#[rr::refined_by("(l, sz, v)" : "loc * page_size * list Z")]
/// As an invariant, a `Page` *exclusively owns* this memory region, and ascribes the value `v` to it.
#[rr::invariant(#type "l" : "<#> v" @ "array_t (int usize_t) (page_size_in_words_nat sz)")]
// TODO: add this once we deal with the Once initialization
//#[rr::exists("MEMORY_CONFIG")]
//#[rr::invariant("once_initialized GLOBAL_MEMORY_LAYOUT MEMORY_CONFIG")]
//#[rr::invariant("page is in range of MEMORY_CONFIG")]
pub struct Page<S: PageState> {
    /// Specification: the `address` has mathematical value `l`.
    #[rr::field("l")]
    address: ConfidentialMemoryAddress,
    /// Specification: the `size` has mathematical value `sz`.
    #[rr::field("sz")]
    size: PageSize,
    /// Specification: the `_marker` has no relevance for the verification.
    #[rr::field("tt")]
    _marker: PhantomData<S>,
}

// We declare Send+Sync on the `Page` because it stores internally a raw pointer, which is
// not safe to pass in a multi-threaded program. But in the case of the `Page` it is safe
// because the `Page` owns the memory associated with pointer and never exposes the raw pointer
// to the outside.
unsafe impl<S> Send for Page<S> where S: PageState {}
unsafe impl<S> Sync for Page<S> where S: PageState {}

impl Page<UnAllocated> {
    /// Creates a page token at the given address in the confidential memory.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that he owns the memory region defined by the address and size
    /// and his ownership is given to the page token.
    ///
    /// # Specification:
    #[rr::params("l", "sz", "v")]
    /// The mathematical values of the two arguments are a memory location `l` and a size `sz`.
    #[rr::args("l", "sz")]
    /// We require ownership of the memory region starting at `l` for size `sz`.
    /// Moreover, `l` needs to be properly aligned for a page of size `sz`.
    /// We view the memory as uninitialized.
    #[rr::requires(#type "l" : "<#> v" @ "array_t (int usize_t) (page_size_in_words_nat sz)")]
    /// Then, we get a properly initialized page starting at `l` of size `sz` with some value `v`.
    #[rr::returns("(l, sz, v)")]
    pub(super) unsafe fn init(address: ConfidentialMemoryAddress, size: PageSize) -> Self {
        Self { address, size, _marker: PhantomData }
    }

    /// Specification:
    #[rr::skip]
    #[rr::params("l", "sz", "v")]
    /// The argument is a page starting at `l` with size `sz` and value `v`.
    #[rr::args("(l, sz, v)")]
    /// We return a page starting at `l` with size `sz`, but with all bytes initialized to zero.
    #[rr::returns("(l, sz, zero_page sz)")]
    pub fn zeroize(mut self) -> Page<Allocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }

    /// Moves a page to the Allocated state after filling its content with the
    /// content of a page located in the non-confidential memory.
    #[rr::skip]
    #[rr::params("l" : "loc", "sz", "v", "l2", "v2")]
    #[rr::args("(l, sz, v)", "l2", "v2")]
    #[rr::requires(#type "l2" : "v2" @ "value_t (UntypedSynType (mk_page_layout sz))")]
    #[rr::ensures(#type "l2" : "v2" @ "value_t (UntypedSynType (mk_page_layout sz))")]
    #[rr::returns("Ok(#(l, sz, v2))")]
    pub fn copy_from_non_confidential_memory(mut self, mut address: NonConfidentialMemoryAddress) -> Result<Page<Allocated>, Error> {
        self.offsets().into_iter().try_for_each(|offset_in_bytes| {
            let non_confidential_address = MemoryLayout::read().non_confidential_address_at_offset(&mut address, offset_in_bytes)?;
            // TODO: describe why below unsafe block is safe in this invocation.
            let data_to_copy = unsafe { non_confidential_address.read() };
            self.write(offset_in_bytes, data_to_copy)?;
            Ok::<(), Error>(())
        })?;
        Ok(Page { address: self.address, size: self.size, _marker: PhantomData })
    }

    /// Returns a collection of all smaller pages that fit within the current page and
    /// are correctly aligned. If this page is the smallest page (4KiB for RISC-V), then
    /// the same page is returned.
    #[rr::skip]
    #[rr::params("MEMORY_CONFIG", "l", "sz", "v")]
    #[rr::args("(l, sz, v)")]
    #[rr::requires("once_initialized GLOBAL_MEMORY_LAYOUT MEMORY_CONFIG")]
    #[rr::returns("subdivide_pages l sz v")]
    pub fn divide(mut self) -> Vec<Page<UnAllocated>> {
        let memory_layout = MemoryLayout::read();
        let smaller_page_size = self.size.smaller().unwrap_or(self.size);
        let number_of_smaller_pages = self.size.in_bytes() / smaller_page_size.in_bytes();
        let page_end = self.end_address_ptr();
        (0..number_of_smaller_pages)
            .map(|i| {
                let offset_in_bytes = i * smaller_page_size.in_bytes();
                // Safety: below unwrap is safe because a size of a larger page is a
                // multiply of a smaller page size, thus we will never exceed the outer page boundary.
                let smaller_page_start =
                    memory_layout.confidential_address_at_offset_bounded(&mut self.address, offset_in_bytes, page_end).unwrap();
                // Safety: The below token creation is safe because the current page owns the entire memory
                // associated with the page and within this function it partitions this memory into smaller
                // disjoined pages, passing the ownership to these smaller memory regions to new tokens.
                unsafe { Page::init(smaller_page_start, smaller_page_size) }
            })
            .collect()
    }

    /// Merges a collection of contiguous pages into a single correctly aligned page.
    ///
    /// # Safety
    ///
    /// * Page is aligned to the new size
    /// * Merged pages are contiguous and cover the entire new size of the future page
    /// * Merged pages are of the same size
    /// * Merged pages are sorted
    pub unsafe fn merge(mut from_pages: Vec<Page<UnAllocated>>, new_size: PageSize) -> Self {
        assert!(from_pages.len() > 2);
        assert!(from_pages[0].address.is_aligned_to(new_size.in_bytes()));
        assert!(new_size.in_bytes() / from_pages[0].size.in_bytes() == from_pages.len());
        assert!(from_pages[0].start_address() + new_size.in_bytes() == from_pages[from_pages.len() - 1].end_address());
        Self::init(from_pages.swap_remove(0).address, new_size)
    }
}

impl Page<Allocated> {
    /// Clears the entire memory content by writing 0s to it and then converts the Page from Allocated to UnAllocated so it can be returned
    /// to the page allocator.
    #[rr::skip]
    #[rr::params("l", "sz", "v")]
    #[rr::args("(l, sz, v)")]
    #[rr::returns("(l, sz, zero_page sz)")]
    pub fn deallocate(mut self) -> Page<UnAllocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }
}

impl<T: PageState> Page<T> {
    #[rr::params("l", "sz", "v")]
    #[rr::args("#(l, sz, v)")]
    #[rr::returns("l")]
    pub fn address(&self) -> &ConfidentialMemoryAddress {
        &self.address
    }

    #[rr::params("l", "sz", "v")]
    #[rr::args("#(l, sz, v)")]
    #[rr::returns("l.2")]
    pub fn start_address(&self) -> usize {
        self.address.as_usize()
    }

    #[rr::params("l", "sz", "v")]
    #[rr::args("#(l, sz, v)")]
    #[rr::returns("l.2 + page_size_in_bytes_Z sz")]
    pub fn end_address(&self) -> usize {
        self.address.as_usize() + self.size.in_bytes()
    }

    // NOTE: round-trip casts are difficult to verify, need support in RefinedRust
    #[rr::only_spec]
    #[rr::params("l", "sz")]
    #[rr::args(#raw "#(-[#l; #sz; #tt])")]
    #[rr::returns("l +ₗ page_size_in_bytes_Z sz")]
    fn end_address_ptr(&self) -> *const usize {
        // TODO: ideally, use strict-provenance API
        self.end_address() as *const usize
    }

    #[rr::params("l", "sz", "v")]
    #[rr::args("#(l, sz, v)")]
    #[rr::returns("#sz")]
    pub fn size(&self) -> &PageSize {
        &self.size
    }

    /// Reads data of size `size_of::<usize>` from a page at a given offset. Error is returned
    /// when an offset that exceeds page size is passed as an argument.
    ///
    /// # Arguments
    ///
    /// * `offset_in_bytes` is an offset from the beginning of the page to which a chunk of data
    /// will be read from the memory. This offset must be a multiply of size_of::(usize) and be
    /// within the page address range, otherwise an Error is returned.
    /// Specification:
    #[rr::params("l", "sz", "v", "off")]
    #[rr::args("#(l, sz, v)", "off")]
    /// Precondition: the offset needs to be divisible by the size of usize.
    #[rr::requires("H_off" : "(ly_size usize_t | off)%Z")]
    /// Precondition: we need to be able to fit a usize at the offset and not exceed the page bounds
    #[rr::requires("H_sz" : "(off + ly_size usize_t ≤ page_size_in_bytes_Z sz)%Z")]
    /// Postcondition: there exists some value `x`...
    #[rr::exists("x" : "Z", "off'" : "nat")]
    /// ...where off is a multiple of usize
    #[rr::ensures("(off = off' * ly_size usize_t)%Z")]
    /// ...that has been read from the byte sequence `v` at offset `off`
    #[rr::ensures("v !! off' = Some x")]
    /// ...and we return an Ok containing the value `x`
    #[rr::returns("Ok(#x)")]
    pub fn read(&self, offset_in_bytes: usize) -> Result<usize, Error> {
        assert!(offset_in_bytes % mem::size_of::<usize>() == 0);
        let data = unsafe {
            // Safety: below add results in a valid confidential memory address because
            // we ensure that it is within the page boundary and page is guaranteed to
            // be entirely inside the confidential memory.
            let pointer = self.address.add(offset_in_bytes, self.end_address_ptr()).unwrap();
            // pointer is guaranteed to be in the range <0;self.size()-size_of::(usize)>

            pointer.read_volatile()
        };
        Ok(data)
    }

    /// Writes data to a page at a given offset. Error is returned if an invalid offset was passed
    /// as an argument.
    ///
    /// # Arguments
    ///
    /// * `offset_in_bytes` is an offset from the beginning of the page to which a chunk of data
    /// will be written to the memory. This offset must be a multiply of size_of::(usize) and be
    /// within the page address range, otherwise an Error is returned.
    /// Specification:
    #[rr::trust_me]
    #[rr::params("l", "sz", "v", "off", "γ", "v2")]
    #[rr::args("(#(l, sz, v), γ)", "off", "v2")]
    /// Precondition: the offset needs to be divisible by the size of usize.
    #[rr::requires("(ly_size usize_t | off)%Z")]
    /// Precondition: we need to be able to fit a usize at the offset and not exceed the page bounds
    #[rr::requires("(off + ly_size usize_t ≤ page_size_in_bytes_Z sz)%Z")]
    #[rr::exists("off'" : "Z")]
    /// Postcondition: off is a multiple of usize
    #[rr::ensures("off = (off' * ly_size usize_t)%Z")]
    /// Postcondition: self has been updated to contain the value `v2` at offset `off`
    #[rr::observe("γ": "(l, sz, <[Z.to_nat off' := v2]> v)")]
    #[rr::returns("Ok(#())")]
    /*
    /// Precondition: the offset needs to be divisible by the size of usize.
    #[rr::requires("(ly_size usize_t | {offset_in_bytes})%Z")]
    /// Precondition: we need to be able to fit a usize at the offset and not exceed the page bounds
    #[rr::requires("({offset_in_bytes} + ly_size usize_t ≤ page_size_in_bytes_Z {self.cur.2})%Z")]
    #[rr::exists("off'" : "Z")]
    /// Postcondition: off is a multiple of usize
    #[rr::ensures("{offset_in_bytes} = (off' * ly_size usize_t)%Z")]
    /// Postcondition: self has been updated to contain the value `v2` at offset `off`
    //#[rr::observe("self": "({self.cur.1}, {self.cur.2}, <[Z.to_nat off' := {value}]> {self.cur.3})")]
    #[rr::observe("self.3": "<[Z.to_nat off' := {value}]> {self.cur.3}")]
    #[rr::returns("Ok(#())")]
    */
    pub fn write(&mut self, offset_in_bytes: usize, value: usize) -> Result<(), Error> {
        assert!(offset_in_bytes % mem::size_of::<usize>() == 0);
        unsafe {
            // Safety: below add results in a valid confidential memory address because
            // we ensure that it is within the page boundary and page is guaranteed to
            // be entirely inside the confidential memory.
            let pointer = self.address.add(offset_in_bytes, self.end_address_ptr()).unwrap();
            // pointer is guaranteed to be in the range <0;self.size()-size_of::(usize)>
            pointer.write_volatile(value);
        };
        Ok(())
    }

    /// Returns all usize-aligned offsets within the page.
    #[rr::skip]
    #[rr::args("#(l, sz, v)")]
    // the values that the iterator will yield?
    #[rr::returns("step_list 0 (ly_size usize_t) (page_size_in_bytes_nat sz)")]
    fn offsets(&self) -> core::iter::StepBy<Range<usize>> {
        (0..self.size.in_bytes()).step_by(mem::size_of::<usize>())
    }

    pub fn end_address_ptr(&self) -> *const usize {
        self.end_address() as *const usize
    }

    #[rr::only_spec]
    #[rr::params("l", "sz", "v", "γ")]
    #[rr::args("(#(l, sz, v), γ)")]
    #[rr::observe("γ": "(l, sz, zero_page sz)")]
    fn clear(&mut self) {
        // Safety: below unwrap() is fine because we iterate over page's offsets and thus always
        // request a write to an offset within the page.
        self.offsets().for_each(
            #[rr::skip]
            #[rr::params("off", "v" : "list Z", "l", "sz")]

            #[rr::args("off")]
            // this should be dispatched by knowing that each argument is an element of the
            // iterator, i.e. be implied by what for_each can guarantee
            #[rr::requires("(ly_size usize_t | off)%Z")]
            #[rr::requires("(off + ly_size usize_t ≤ page_size_in_bytes_Z sz)%Z")]

            #[rr::exists("off'")]
            #[rr::ensures("off = (off' * ly_size usize_t)%Z")]
            #[rr::capture("self" : "(l, sz, v)" -> "(l, sz, <[Z.to_nat off' := 0]> v)")]
            |offset_in_bytes| self.write(offset_in_bytes, 0).unwrap(),
        );
    }
}
