// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::MemoryLayout;
use crate::error::Error;
use pointers_utility::ptr_byte_add_mut;

/// The wrapper over a raw pointer that is guaranteed to be an address located in the non-confidential memory region.
#[repr(transparent)]
#[derive(Debug)]
#[rr::refined_by("l" : "loc")]
#[rr::context("onceG Σ memory_layout")]
#[rr::exists("MEMORY_CONFIG")]
#[rr::invariant(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
#[rr::invariant("(MEMORY_CONFIG.(non_conf_start).2 ≤ l.2 < MEMORY_CONFIG.(non_conf_end).2)%Z")]
pub struct NonConfidentialMemoryAddress(#[rr::field("l")] *mut usize);

#[rr::context("onceG Σ memory_layout")]
impl NonConfidentialMemoryAddress {
    /// Constructs an address in a non-confidential memory. Returns error if the address is outside non-confidential
    /// memory.
    #[rr::trust_me]
    #[rr::params("l", "bounds")]
    #[rr::args("l")]
    #[rr::requires(#iris "once_status \"MEMORY_LAYOUT\" (Some bounds)")]
    #[rr::requires("bounds.(non_conf_start).2 ≤ l.2")]
    #[rr::requires("l.2 < bounds.(non_conf_end).2")]
    #[rr::returns("Ok (#l)")]
    pub fn new(address: *mut usize) -> Result<Self, Error> {
        match MemoryLayout::read().is_in_non_confidential_range(address) {
            false => Err(Error::AddressNotInNonConfidentialMemory()),
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
        let pointer = ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(|_| Error::AddressNotInNonConfidentialMemory())?;
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

    #[rr::only_spec]
    #[rr::params("l")]
    #[rr::args("#l")]
    #[rr::returns("l.2")]
    pub fn usize(&self) -> usize {
        self.0 as usize
    }
}
