// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::PageSize;
use crate::core::control_data::{DigestType, MeasurementDigest};
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout, NonConfidentialMemoryAddress};
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
            let non_confidential_address = MemoryLayout::read()
                .non_confidential_address_at_offset(&mut address, offset_in_bytes)
                .map_err(|_| Error::AddressNotInNonConfidentialMemory())?;
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
    pub fn deallocate(mut self) -> Page<UnAllocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }
}

impl<T: PageState> Page<T> {
    pub const ENTRY_SIZE: usize = mem::size_of::<usize>();

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
        assert!(offset_in_bytes % Self::ENTRY_SIZE == 0);
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
        ensure!(offset_in_bytes % Self::ENTRY_SIZE == 0, Error::AddressNotAligned())?;
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

    /// Extends the digest with the guest physical address and the content of the page.
    pub fn measure(&self, digest: &mut MeasurementDigest, guest_physical_address: usize) {
        use sha2::Digest;
        let mut hasher = DigestType::new_with_prefix(digest.clone());
        hasher.update(guest_physical_address.to_le_bytes());
        // below unsafe is ok because the page has been initialized and it owns the entire memory region.
        // We are creating a slice of bytes, so the number of elements in the slice is the same as the size of the page.
        let slice: &[u8] = unsafe { core::slice::from_raw_parts(self.address().to_ptr(), self.size().in_bytes()) };
        hasher.update(&slice);
        hasher.finalize_into(digest);
    }

    /// Returns all usize-aligned offsets within the page.
    pub fn offsets(&self) -> core::iter::StepBy<Range<usize>> {
        (0..self.size.in_bytes()).step_by(Self::ENTRY_SIZE)
    }

    pub fn end_address_ptr(&self) -> *const usize {
        self.end_address() as *const usize
    }

    fn clear(&mut self) {
        // Safety: below unwrap() is fine because we iterate over page's offsets and thus always
        // request a write to an offset within the page.
        self.offsets().for_each(|offset_in_bytes| self.write(offset_in_bytes, 0).unwrap());
    }
}

// We declare Send+Sync on the `Page` because it stores internally a raw pointer, which is
// not safe to pass in a multi-threaded program. But in the case of the `Page` it is safe
// because the `Page` owns the memory associated with pointer and never exposes the raw pointer
// to the outside.
unsafe impl<S> Send for Page<S> where S: PageState {}
unsafe impl<S> Sync for Page<S> where S: PageState {}
