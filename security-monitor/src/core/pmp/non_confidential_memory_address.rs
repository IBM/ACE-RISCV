// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::pmp::MemoryLayout;
use crate::error::Error;

#[repr(transparent)]
#[derive(Debug)]
pub struct NonConfidentialMemoryAddress(pub(super) *mut usize);

// We need to declare Send+Sync on the `NonConfidentialMemoryAddress` because it stores internally a raw pointer and
// raw pointers are not safe to pass in a multi-threaded program. But in the case of NonConfidentialMemoryAddress it
// is safe because we never expose raw pointers outside the NonConfidentialMemoryAddress.
unsafe impl Send for NonConfidentialMemoryAddress {}
unsafe impl Sync for NonConfidentialMemoryAddress {}

impl NonConfidentialMemoryAddress {
    /// Constructs an address in a non-confidential memory. Returns error if the address
    /// is outside non-confidential memory.
    pub fn new(address: usize) -> Result<Self, Error> {
        let pointer = address as *mut usize;
        // We check that the address is within the non-confidential memory range.
        // This is equavalent to ensure that it does not point to confidential memory as long
        // as memory is correctly splitted during the initialization procedure.
        match MemoryLayout::get().is_in_non_confidential_range(pointer) {
            false => Err(Error::MemoryAccessAuthorization()),
            true => Ok(Self(pointer)),
        }
    }

    pub unsafe fn read(&self) -> usize {
        self.0.read_volatile()
    }

    pub fn usize(&self) -> usize {
        self.0 as usize
    }
}
