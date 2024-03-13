// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use pointers_utility::{ptr_byte_add_mut, ptr_byte_offset};

/// The wrapper over a raw pointer that is guaranteed to be an address located in the confidential memory region.
#[repr(transparent)]
#[derive(Debug, PartialEq)]
pub struct ConfidentialMemoryAddress(*mut usize);

impl ConfidentialMemoryAddress {
    pub(super) fn new(address: *mut usize) -> Self {
        Self(address)
    }

    // TODO: check if needed. If yes, make sure the raw pointer is not used incorrectly Currently we only use it during
    // creation of the heap allocator structure. It would be good to get rid of this because it requires extra safety
    // guarantees for parallel execution of the security monitor
    pub unsafe fn into_mut_ptr(self) -> *mut usize {
        self.0
    }

    pub unsafe fn to_ptr(&self) -> *const u8 {
        self.0 as *const u8
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn is_aligned_to(&self, align: usize) -> bool {
        self.0.is_aligned_to(align)
    }

    pub fn offset_from(&self, pointer: *const usize) -> isize {
        ptr_byte_offset(pointer, self.0)
    }

    /// Creates a new confidential memory address at given offset. Error is returned if the resulting address exceeds
    /// the upper boundary.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the address at given offset is still within the confidential memory region.
    pub unsafe fn add(&self, offset_in_bytes: usize, upper_bound: *const usize) -> Result<ConfidentialMemoryAddress, Error> {
        let pointer = ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(|_| Error::MemoryAccessAuthorization())?;
        Ok(ConfidentialMemoryAddress(pointer))
    }

    /// Reads usize-sized sequence of bytes from the confidential memory region.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the pointer is not used by two threads simultaneously. See `ptr::read_volatile` for
    /// safety concerns
    pub unsafe fn read_volatile(&self) -> usize {
        self.0.read_volatile()
    }

    /// Writes usize-sized sequence of bytes to the confidential memory region.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the pointer is not used by two threads simultaneously. See `ptr::write_volatile` for
    /// safety concerns
    pub unsafe fn write_volatile(&self, value: usize) {
        self.0.write_volatile(value);
    }
}
