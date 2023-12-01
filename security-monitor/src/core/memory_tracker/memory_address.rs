// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use core::ops::Range;
use spin::Once;

/// Below global variables are set up during the boot process (the init
/// function) and never change later -- this is guaranteed by Once<>. They
/// describe the memroy region containing the confidential memory and OpenSBI.
pub static CONFIDENTIAL_MEMORY_RANGE: Once<Range<usize>> = Once::new();

#[repr(transparent)]
#[derive(Debug, PartialEq)]
pub struct ConfidentialMemoryAddress(pub(super) *mut usize);

impl ConfidentialMemoryAddress {
    pub fn as_mut_ptr(&mut self) -> *mut usize {
        self.0
    }

    pub fn as_ptr(&self) -> *const usize {
        self.0 as *const usize
    }
}

// TODO: NonConfidentialMemoryAddress should use raw pointers and not usize to represent addresses.
#[repr(transparent)]
#[derive(Debug)]
pub struct NonConfidentialMemoryAddress(usize);

impl NonConfidentialMemoryAddress {
    pub fn new(address: usize) -> Result<Self, Error> {
        use crate::error::NOT_INITIALIZED_CONFIDENTIAL_MEMORY;
        // TODO: We should check that the address is within the non-confidential memory range.
        // This is equavalent to ensure that it does not point to confidential memory as long
        // as memory is correctly splitted during the initialization procedure.
        match CONFIDENTIAL_MEMORY_RANGE.get().expect(NOT_INITIALIZED_CONFIDENTIAL_MEMORY).contains(&address) {
            true => Err(Error::MemoryAccessAuthorization()),
            false => Ok(Self(address)),
        }
    }

    /// creates a non-confidential address by offseting the current address. An error is returned
    /// if the resulting address is in the confidential memory.
    pub fn add(&self, offset_in_bytes: usize) -> Result<Self, Error> {
        let incremented_address = self.0.checked_add(offset_in_bytes).ok_or(Error::MemoryAccessAuthorization())?;
        Self::new(incremented_address)
    }

    pub unsafe fn read(&self) -> usize {
        (self.0 as *const usize).read_volatile()
    }

    pub fn usize(&self) -> usize {
        self.0
    }
}
