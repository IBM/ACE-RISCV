// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![rr::import("ace.theories.result", "result")]
use crate::error::Error;
use pointers_utility::{ptr_byte_add_mut, ptr_byte_offset};

/// The wrapper over a raw pointer that is guaranteed to be an address located in the confidential memory region.
#[repr(transparent)]
#[derive(Debug, PartialEq)]
#[rr::refined_by("l" : "loc")]
pub struct ConfidentialMemoryAddress(#[rr::field("l")] *mut usize);

impl ConfidentialMemoryAddress {
    #[rr::params("l")]
    #[rr::args("l")]
    #[rr::returns("l")]
    pub(super) fn new(address: *mut usize) -> Self {
        Self(address)
    }

    // TODO: check if needed. If yes, make sure the raw pointer is not used incorrectly
    // Currently we only use it during creation of the heap allocator structure. It
    // would be good to get rid of this because it requires extra safety guarantees for
    // parallel execution of the security monitor
    #[rr::params("l")]
    #[rr::args("l")]
    #[rr::returns("l")]
    pub unsafe fn into_mut_ptr(self) -> *mut usize {
        self.0
    }

    pub unsafe fn to_ptr(&self) -> *const u8 {
        self.0 as *const u8
    }

    // TODO: verify
    #[rr::only_spec]
    #[rr::params("l")]
    #[rr::args("#l")]
    #[rr::returns("l.2")]
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
    // TODO: can we require the offset to be a multiple of usize?
    #[rr::only_spec]
    #[rr::params("l", "off", "lmax")]
    #[rr::args("#l", "off", "lmax")]
    #[rr::requires("l.2 + off < lmax.2")]
    #[rr::returns("Ok(#(l +ₗ off))")]
    pub unsafe fn add(&self, offset_in_bytes: usize, upper_bound: *const usize) -> Result<ConfidentialMemoryAddress, Error> {
        let pointer = ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(|_| Error::AddressNotInConfidentialMemory())?;
        Ok(ConfidentialMemoryAddress(pointer))
    }

    /// Reads usize-sized sequence of bytes from the confidential memory region.
    ///
    /// # Safety
    /// Caller must ensure that the pointer is not used by two threads simultaneously. See `ptr::read_volatile` for
    /// safety concerns
    // TODO: currently only_spec because shim registration for read_volatile doesn't work
    #[rr::only_spec]
    #[rr::params("l", "z", "lft_el")]
    #[rr::args("#l")]
    #[rr::requires(#iris "l ◁ₗ[π, Shared lft_el] #z @ ◁ int usize_t")]
    #[rr::returns("z")]
    pub unsafe fn read_volatile<'a>(&'a self) -> usize {
        self.0.read_volatile()
    }

    /// Writes usize-sized sequence of bytes to the confidential memory region.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the pointer is not used by two threads simultaneously. See `ptr::write_volatile` for
    /// safety concerns
    // TODO: currently only_spec because shim registration for write_volatile doens't work
    #[rr::only_spec]
    #[rr::params("l", "z", "x")]
    #[rr::args("#l", "x")]
    #[rr::requires(#type "l" : "z" @ "int usize_t")]
    #[rr::ensures(#type "l" : "x" @ "int usize_t")]
    pub unsafe fn write_volatile(&self, value: usize) {
        self.0.write_volatile(value);
    }
}
