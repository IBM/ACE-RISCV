// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_tracker::{ConfidentialMemoryAddress, NonConfidentialMemoryAddress};
use crate::core::mmu::PageSize;
use crate::error::Error;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::ops::Range;

pub trait PageState {}

pub enum UnAllocated {}
pub enum Allocated {}

impl PageState for UnAllocated {}
impl PageState for Allocated {}

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
        // The below copy is secure because we checked that any address in the
        // address range belongs to the confidential memory (no overlapping).
        self.offsets().for_each(|offset| {
            // Safety: we must read usize from the non-confidential memory because the `self.write`
            // only supports writing usize.
            let data_to_copy = unsafe { ((address.usize() + offset) as *mut usize).read_volatile() };
            self.write(offset, data_to_copy);
        });
        Ok(Page { address: self.address, size: self.size, _marker: PhantomData })
    }

    /// This function divides the current page into smaller pages if possible.
    /// If this page is the smalles page (4KiB for RISC-V) then the same page is
    /// returned.
    pub fn divide(mut self) -> Vec<Page<UnAllocated>> {
        let smaller_size = self.size.smaller().unwrap_or(self.size);
        let number_of_smaller_pages = self.size.in_bytes() / smaller_size.in_bytes();
        (0..number_of_smaller_pages)
            .map(|i| {
                let smaller_page_address = unsafe { self.address.as_mut_ptr().byte_add(i * smaller_size.in_bytes()) };
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

    pub fn size(&self) -> &PageSize {
        &self.size
    }

    // Use this function to iterate over all usize chunks of data in a page
    fn offsets(&self) -> core::iter::StepBy<Range<usize>> {
        (0..self.size.in_bytes()).step_by(core::mem::size_of::<usize>())
    }

    pub fn read(&self, offset_in_bytes: usize) -> usize {
        assert!(offset_in_bytes + core::mem::size_of::<usize>() <= self.size.in_bytes());
        unsafe { self.address.as_ptr().byte_add(offset_in_bytes).read_volatile() }
    }

    pub fn write(&mut self, offset_in_bytes: usize, value: usize) {
        assert!(offset_in_bytes + core::mem::size_of::<usize>() <= self.size.in_bytes());
        unsafe { self.address.as_mut_ptr().byte_add(offset_in_bytes).write_volatile(value) };
    }

    fn clear(&mut self) {
        // TODO: performance optimisation. Write word/double word instead of a byte
        self.offsets().for_each(|offset_in_bytes| self.write(offset_in_bytes, 0));
    }
}
