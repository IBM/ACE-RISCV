// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::pmp::MemoryLayout;
use crate::error::Error;
use pointers_utility::ptr_byte_add_mut;

/// `NonConfidentialMemoryAddress` represent an address in the non-confidential memory.
/// The constructor ensures that the address from which this type is instantiated is
/// inside the non-confidential memory.
#[repr(transparent)]
#[derive(Debug)]
pub struct NonConfidentialMemoryAddress(*mut usize);

impl NonConfidentialMemoryAddress {
    /// Constructs an address in a non-confidential memory. Returns error if the address
    /// is outside non-confidential memory.
    pub fn new(address: *mut usize) -> Result<Self, Error> {
        // We check that the address is within the non-confidential memory range.
        // This is equavalent to ensure that it does not point to confidential memory as long
        // as memory is correctly splitted during the initialization procedure.
        match MemoryLayout::get().is_in_non_confidential_range(address) {
            false => Err(Error::MemoryAccessAuthorization()),
            true => Ok(Self(address)),
        }
    }

    /// Creates a new non-confidential memory address at given offset. Error is returned if the resulting
    /// address exceeds the upper boundary.
    ///
    /// # Safety
    ///
    /// The caller takes the responsibility to ensure that the address advanced by the offset is still in the
    /// confidential memory.
    pub unsafe fn add(
        &self, offset_in_bytes: usize, upper_bound: *const usize,
    ) -> Result<NonConfidentialMemoryAddress, Error> {
        let pointer =
            ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(|_| Error::MemoryAccessAuthorization())?;
        Ok(NonConfidentialMemoryAddress(pointer))
    }

    /// Reads the content of the non-confidential memory.
    ///
    /// # Safety
    ///
    /// We need to ensure the pointer is not used by two threads simultaneously.
    /// See `ptr::read_volatile` for safety concerns.
    pub unsafe fn read(&self) -> usize {
        self.0.read_volatile()
    }

    pub fn usize(&self) -> usize {
        self.0 as usize
    }
}
