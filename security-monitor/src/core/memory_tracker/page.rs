// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_tracker::{ConfidentialMemoryAddress, NonConfidentialMemoryAddress};
use crate::core::mmu::PageSize;
use crate::error::Error;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem;
use core::ops::Range;
use pointers_utility::{ptr_byte_add, ptr_byte_add_mut};

pub trait PageState {}

pub enum UnAllocated {}
pub enum Allocated {}

impl PageState for UnAllocated {}
impl PageState for Allocated {}

// We need to declare Send+Sync on the `Page` because Page stores internally a raw pointer and
// raw pointers are not safe to pass in a multi-threaded program. But in the case of Page it is
// safe because we never expose raw pointers outside the page.
unsafe impl<S> Send for Page<S> where S: PageState {}
unsafe impl<S> Sync for Page<S> where S: PageState {}

#[derive(Debug)]
pub struct Page<S: PageState> {
    address: ConfidentialMemoryAddress,
    size: PageSize,
    _marker: PhantomData<S>,
}

impl Page<UnAllocated> {
    // this constructor is visible only to the memory module, so only the
    // memory tracker can create new pages.
    pub(super) fn init(address: ConfidentialMemoryAddress, size: PageSize) -> Self {
        Self { address, size, _marker: PhantomData }
    }

    pub fn zeroize(mut self) -> Page<Allocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }

    /// Moves a page to the Allocated state after filling its content with the
    /// content of a page located in the non-confidential memory.
    pub fn copy_from_non_confidential_memory(
        mut self, address: NonConfidentialMemoryAddress,
    ) -> Result<Page<Allocated>, Error> {
        self.offsets().into_iter().try_for_each(|offset_in_bytes| {
            // Safety: we must read usize from the non-confidential memory because the `self.write`
            // only supports writing usize.
            let data_to_copy = unsafe { address.add(offset_in_bytes)?.read() };
            self.write(offset_in_bytes, data_to_copy)?;
            Ok::<(), Error>(())
        })?;
        Ok(Page { address: self.address, size: self.size, _marker: PhantomData })
    }

    /// This function divides the current page into smaller pages if possible.
    /// If this page is the smallest page (4KiB for RISC-V), then the same page is
    /// returned.
    pub fn divide(mut self) -> Vec<Page<UnAllocated>> {
        let smaller_size = self.size.smaller().unwrap_or(self.size);
        let number_of_smaller_pages = self.size.in_bytes() / smaller_size.in_bytes();
        let page_start = self.address.as_mut_ptr();
        let page_end = self.end_address_ptr();
        (0..number_of_smaller_pages)
            .map(|i| {
                let offset_in_bytes = i * smaller_size.in_bytes();
                // Safety: below line will panic in case of a programming bug where we defined that
                // a page can store a certain number of smaller pages but it cannot. This should never
                // happen in a correctly implemented (and proven) code.
                // Below pointer arithmetic should never overflow unless we have misconfigured system where
                // the system is supposed to handle memory pages of sizes exceeded what usize can address.
                let smaller_page_address = ptr_byte_add_mut(page_start, offset_in_bytes, page_end).unwrap();
                Page::init(ConfidentialMemoryAddress(smaller_page_address), smaller_size)
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
        self.address.as_ptr() as usize
    }

    pub fn end_address(&self) -> usize {
        self.address.as_ptr() as usize + self.size.in_bytes()
    }

    pub fn end_address_ptr(&self) -> *const usize {
        self.end_address() as *const usize
    }

    pub fn size(&self) -> &PageSize {
        &self.size
    }

    // Use this function to iterate over all usize chunks of data in a page
    fn offsets(&self) -> core::iter::StepBy<Range<usize>> {
        (0..self.size.in_bytes()).step_by(mem::size_of::<usize>())
    }

    pub fn read(&self, offset_in_bytes: usize) -> Result<usize, Error> {
        assert!(offset_in_bytes <= self.size().in_bytes() - mem::size_of::<usize>());
        assert!(offset_in_bytes % mem::size_of::<usize>() == 0);
        let pointer = ptr_byte_add(self.address.as_ptr(), offset_in_bytes, self.end_address_ptr())?;
        let data = unsafe { pointer.read_volatile() };
        Ok(data)
    }

    pub fn write(&mut self, offset_in_bytes: usize, value: usize) -> Result<(), Error> {
        assert!(offset_in_bytes <= self.size().in_bytes() - mem::size_of::<usize>());
        assert!(offset_in_bytes % mem::size_of::<usize>() == 0);
        let pointer = ptr_byte_add_mut(self.address.as_mut_ptr(), offset_in_bytes, self.end_address_ptr())?;
        unsafe { pointer.write_volatile(value) };
        Ok(())
    }

    fn clear(&mut self) {
        // Safety: below unwrap() is fine because we iterate over page's offsets and thus always
        // request a write to an offset within the page.
        self.offsets().for_each(|offset_in_bytes| self.write(offset_in_bytes, 0).unwrap());
    }
}
