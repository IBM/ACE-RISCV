// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::mmu::PageSize;
use crate::core::pmp::{ConfidentialMemoryAddress, MemoryLayout, NonConfidentialMemoryAddress};
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

// We need to declare Send+Sync on the `Page` because Page stores internally a raw pointer and
// raw pointers are not safe to pass in a multi-threaded program. But in the case of Page it is
// safe because we never expose raw pointers outside the Page.
unsafe impl<S> Send for Page<S> where S: PageState {}
unsafe impl<S> Sync for Page<S> where S: PageState {}

#[derive(Debug)]
pub struct Page<S: PageState> {
    address: ConfidentialMemoryAddress,
    size: PageSize,
    _marker: PhantomData<S>,
}

impl Page<UnAllocated> {
    /// Creates a page token at the given address in the confidential memory.
    pub(super) fn init(address: ConfidentialMemoryAddress, size: PageSize) -> Self {
        // this constructor is visible only to the memory module, so only the
        // memory tracker can create new pages.
        Self { address, size, _marker: PhantomData }
    }

    pub fn zeroize(mut self) -> Page<Allocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }

    /// Moves a page to the Allocated state after filling its content with the
    /// content of a page located in the non-confidential memory.
    pub fn copy_from_non_confidential_memory(
        mut self, mut address: NonConfidentialMemoryAddress,
    ) -> Result<Page<Allocated>, Error> {
        self.offsets().into_iter().try_for_each(|offset_in_bytes| {
            // Safety: we must read usize from the non-confidential memory because the `self.write`
            // only supports writing usize.
            let non_confidential_address =
                MemoryLayout::get().non_confidential_address_at_offset(&mut address, offset_in_bytes)?;
            let data_to_copy = unsafe { non_confidential_address.read() };
            self.write(offset_in_bytes, data_to_copy)?;
            Ok::<(), Error>(())
        })?;
        Ok(Page { address: self.address, size: self.size, _marker: PhantomData })
    }

    /// This function divides the current page into smaller pages if possible.
    /// If this page is the smallest page (4KiB for RISC-V), then the same page is
    /// If this page is the smallest page (4KiB for RISC-V), then the same page is
    /// returned.
    pub fn divide(mut self) -> Vec<Page<UnAllocated>> {
        let memory_layout = MemoryLayout::get();
        let smaller_size = self.size.smaller().unwrap_or(self.size);
        let number_of_smaller_pages = self.size.in_bytes() / smaller_size.in_bytes();
        let page_end = self.end_address_ptr();
        (0..number_of_smaller_pages)
            .map(|i| {
                let offset_in_bytes = i * smaller_size.in_bytes();
                // Safety: below line will panic in case of a programming bug where we defined that
                // a page can store a certain number of smaller pages but it cannot. This should never
                // happen in a correctly implemented (and proven) code.
                // Below pointer arithmetic should never overflow unless we have misconfigured system where
                // the system is supposed to handle memory pages of sizes exceeded what usize can address.
                let smaller_page_start = memory_layout
                    .confidential_address_at_offset_bounded(&mut self.address, offset_in_bytes, page_end)
                    .unwrap();
                Page::init(smaller_page_start, smaller_size)
            })
            .collect()
    }
}

impl Page<Allocated> {
    /// Clears the entire memory content by writing 0s to it and then converts
    /// the Page from Allocated to UnAllocated so it can be returned to the
    /// memory tracker.
    pub fn deallocate(mut self) -> Page<UnAllocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }
}

impl<T: PageState> Page<T> {
    pub fn start_address(&self) -> usize {
        self.address.as_usize()
    }

    pub fn end_address(&self) -> usize {
        self.address.as_usize() + self.size.in_bytes()
    }

    fn end_address_ptr(&self) -> *const usize {
        self.end_address() as *const usize
    }

    pub fn size(&self) -> &PageSize {
        &self.size
    }

    /// Returns all usize-aligned offsets within the page.
    fn offsets(&self) -> core::iter::StepBy<Range<usize>> {
        (0..self.size.in_bytes()).step_by(mem::size_of::<usize>())
    }

    /// Reads data from a page at a given offset.
    ///
    /// # Arguments
    ///
    /// * `offset_in_bytes` is an offset from the beginning of the page to which a chunk of data
    /// will be read from the memory. This offset must be a multiply of size_of::(usize) and be
    /// within the page address range, otherwise an Error is returned.
    ///
    /// # Return
    ///
    /// A chunk of data of size `size_of::<usize>` is returned, if the
    /// valid offset was passed as an argument.
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

    /// Writes data to a page at a given offset.
    ///
    /// # Arguments
    ///
    /// * `offset_in_bytes` is an offset from the beginning of the page to which a chunk of data
    /// will be written to the memory. This offset must be a multiply of size_of::(usize) and be
    /// within the page address range, otherwise an Error is returned.
    ///
    /// # Return
    ///
    /// Error is returned if an invalid offset was passed as an argument.
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

    fn clear(&mut self) {
        // Safety: below unwrap() is fine because we iterate over page's offsets and thus always
        // request a write to an offset within the page.
        self.offsets().for_each(|offset_in_bytes| self.write(offset_in_bytes, 0).unwrap());
    }
}
