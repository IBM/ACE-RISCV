// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout, NonConfidentialMemoryAddress};
use crate::core::memory_protector::PageSize;
use crate::error::Error;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem;
use core::ops::Range;

pub trait PageState {}

pub enum UnAllocated {}
pub enum Allocated {}

impl PageState for UnAllocated {}
impl PageState for Allocated {}

#[derive(Debug)]
pub struct Page<S: PageState> {
    address: ConfidentialMemoryAddress,
    size: PageSize,
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
    pub(super) unsafe fn init(address: ConfidentialMemoryAddress, size: PageSize) -> Self {
        Self { address, size, _marker: PhantomData }
    }

    pub fn zeroize(mut self) -> Page<Allocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }

    /// Moves a page to the Allocated state after filling its content with the
    /// content of a page located in the non-confidential memory.
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
    /// are correctly alligned. If this page is the smallest page (4KiB for RISC-V), then
    /// the same page is returned.
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

    /// Merges a collection of contiguous pages alligned to the specified page size into a single page.
    ///
    /// # Safety
    ///
    /// * Page is aligned to the new size
    /// * Merged pages are contiguous and cover the entire new size of the future page
    /// * Merged pages are of the same size
    /// * Merged pages are sorted
    pub unsafe fn merge(mut from_pages: Vec<Page<UnAllocated>>, new_size: PageSize) -> Self {
        let number_of_pages = from_pages.len();
        assert!(number_of_pages > 2);
        assert!(from_pages[0].address.is_aligned_to(new_size.in_bytes()));
        assert!(new_size.in_bytes() / from_pages[0].size.in_bytes() == number_of_pages);
        assert!(from_pages[0].start_address() + new_size.in_bytes() == from_pages[number_of_pages - 1].end_address());
        let mut first_page = from_pages.swap_remove(0);
        first_page.size = new_size;
        first_page
    }
}

impl Page<Allocated> {
    /// Clears the entire memory content by writing 0s to it and then converts the Page from Allocated to UnAllocated so it can be returned
    /// to the page allocator.
    pub fn deallocate(mut self) -> Page<UnAllocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }
}

impl<T: PageState> Page<T> {
    pub fn address(&self) -> &ConfidentialMemoryAddress {
        &self.address
    }

    pub fn start_address(&self) -> usize {
        self.address.as_usize()
    }

    pub fn end_address(&self) -> usize {
        self.address.as_usize() + self.size.in_bytes()
    }

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
    pub fn read(&self, offset_in_bytes: usize) -> Result<usize, Error> {
        assert!(offset_in_bytes % mem::size_of::<usize>() == 0);
        let data = unsafe {
            // Safety: below add results in a valid confidential memory address because
            // we ensure that it is within the page boundary and page is guaranteed to
            // be entirely inside the confidential memory.
            let pointer = self.address.add(offset_in_bytes, self.end_address_ptr())?;
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
    pub fn write(&mut self, offset_in_bytes: usize, value: usize) -> Result<(), Error> {
        assure!(offset_in_bytes % mem::size_of::<usize>() == 0, Error::MemoryAccessAuthorization())?;
        unsafe {
            // Safety: below add results in a valid confidential memory address because
            // we ensure that it is within the page boundary and page is guaranteed to
            // be entirely inside the confidential memory.
            let pointer = self.address.add(offset_in_bytes, self.end_address_ptr())?;
            // pointer is guaranteed to be in the range <0;self.size()-size_of::(usize)>
            pointer.write_volatile(value);
        };
        Ok(())
    }

    /// Returns all usize-aligned offsets within the page.
    fn offsets(&self) -> core::iter::StepBy<Range<usize>> {
        (0..self.size.in_bytes()).step_by(mem::size_of::<usize>())
    }

    fn end_address_ptr(&self) -> *const usize {
        self.end_address() as *const usize
    }

    fn clear(&mut self) {
        // Safety: below unwrap() is fine because we iterate over page's offsets and thus always
        // request a write to an offset within the page.
        self.offsets().for_each(|offset_in_bytes| self.write(offset_in_bytes, 0).unwrap());
    }
}
