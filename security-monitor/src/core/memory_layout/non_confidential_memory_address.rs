// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::MemoryLayout;
use crate::error::Error;
use pointers_utility::ptr_byte_add_mut;

/// The wrapper over a raw pointer that is guaranteed to be an address located in the non-confidential memory region.
#[repr(transparent)]
#[derive(Debug)]
pub struct NonConfidentialMemoryAddress(*mut usize);

impl NonConfidentialMemoryAddress {
    /// Constructs an address in a non-confidential memory. Returns error if the address is outside non-confidential
    /// memory.
    pub fn new(address: *mut usize) -> Result<Self, Error> {
        match MemoryLayout::read().is_in_non_confidential_range(address) {
            false => Err(Error::MemoryAccessAuthorization()),
            true => Ok(Self(address)),
        }
    }

    /// Creates a new non-confidential memory address at given offset. Returns error if the resulting address exceeds
    /// the upper boundary.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the address advanced by the offset is still within the non-confidential memory
    /// region.
    pub unsafe fn add(&self, offset_in_bytes: usize, upper_bound: *const usize) -> Result<NonConfidentialMemoryAddress, Error> {
        let pointer = ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(|_| Error::MemoryAccessAuthorization())?;
        Ok(NonConfidentialMemoryAddress(pointer))
    }

    /// Reads usize-sized sequence of bytes from the non-confidential memory region.
    ///
    /// # Safety
    ///
    /// We need to ensure the pointer is not used by two threads simultaneously. See `ptr::read_volatile` for safety
    /// concerns.
    pub unsafe fn read(&self) -> usize {
        self.0.read_volatile()
    }

    /// Writes usize-sized sequence of bytes to the non-confidential memory region.
    ///
    /// # Safety
    ///
    /// We need to ensure the pointer is not used by two threads simultaneously. See `ptr::write_volatile` for safety
    /// concerns.
    pub unsafe fn write(&self, value: usize) {
        self.0.write_volatile(value);
    }

    pub fn as_ptr(&self) -> *const usize {
        self.0
    }

    pub fn usize(&self) -> usize {
        self.0 as usize
    }
}
