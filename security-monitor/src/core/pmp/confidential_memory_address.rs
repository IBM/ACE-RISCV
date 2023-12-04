// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use pointers_utility::{ptr_byte_add_mut, ptr_byte_offset};

#[repr(transparent)]
#[derive(Debug, PartialEq)]
pub struct ConfidentialMemoryAddress(pub(super) *mut usize);

// We need to declare Send+Sync on the `ConfidentialMemoryAddress` because it stores internally a raw pointer and
// raw pointers are not safe to pass in a multi-threaded program. But in the case of ConfidentialMemoryAddress it 
// is safe because we never expose raw pointers outside the ConfidentialMemoryAddress.
unsafe impl Send for ConfidentialMemoryAddress {}
unsafe impl Sync for ConfidentialMemoryAddress {}

impl ConfidentialMemoryAddress {
    pub fn into_mut_ptr(self) -> *mut usize {
        self.0
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

    /// Creates a new confidential memory address at given offset. Error is returned if the resulting
    /// address exceeds the upper boundary.
    ///
    /// Safety
    ///
    /// The caller takes the responsibility to ensure that the address at given offset is still in the
    /// confidential memory.
    pub unsafe fn add(
        &self, offset_in_bytes: usize, upper_bound: *const usize,
    ) -> Result<ConfidentialMemoryAddress, Error> {
        let pointer =
            ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(|_| Error::MemoryAccessAuthorization())?;
        Ok(ConfidentialMemoryAddress(pointer))
    }

    pub unsafe fn read_volatile(&self) -> usize {
        self.0.read_volatile()
    }

    pub unsafe fn write_volatile(&self, value: usize) {
        self.0.write_volatile(value);
    }
}
