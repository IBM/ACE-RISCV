// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use pointers_utility::{ptr_byte_add_mut, ptr_byte_offset};

/// The wrapper over a raw pointer that is guaranteed to be an address located in the confidential memory region.
#[repr(transparent)]
#[derive(Debug, PartialEq)]
/// Model: The memory address is represented by the location in memory.
#[rr::refined_by("l" : "loc")]
/// We require the ghost state for the global memory layout to be available.
#[rr::context("onceG Σ memory_layout")]
/// Invariant: The global memory layout has been initialized.
#[rr::exists("MEMORY_CONFIG")]
#[rr::invariant(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
/// Invariant: The address is in the confidential part of the memory layout.
#[rr::invariant("(MEMORY_CONFIG.(conf_start).2 ≤ l.2 < MEMORY_CONFIG.(conf_end).2)%Z")]
pub struct ConfidentialMemoryAddress(#[rr::field("l")] *mut usize);

/// Verification: We require the ghost state for the global memory layout to be available.
#[rr::context("onceG Σ memory_layout")]
impl ConfidentialMemoryAddress {
    #[rr::params("MEMORY_CONFIG")]
    /// Precondition: The global memory layout is initialized.
    #[rr::requires(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
    /// Precondition: The address is in the confidential region of the global memory layout.
    #[rr::requires("(MEMORY_CONFIG.(conf_start).2 ≤ address.2 < MEMORY_CONFIG.(conf_end).2)%Z")]
    #[rr::returns("address")]
    // TODO this should be unsafe
    pub(super) fn new(address: *mut usize) -> Self {
        Self(address)
    }

    #[rr::returns("self")]
    pub fn to_ptr(&self) -> *const u8 {
        self.0 as *const u8
    }

    #[rr::returns("self.2")]
    pub fn as_usize(&self) -> usize {
        self.0.addr()
    }

    #[rr::only_spec]
    /// Postcondition: Verifies that the pointer is aligned to the given alignment.
    #[rr::returns("bool_decide (self `aligned_to` (Z.to_nat align))")]
    pub fn is_aligned_to(&self, align: usize) -> bool {
        self.0.is_aligned_to(align)
    }

    /// Postcondition: Compute the offset.
    #[rr::returns("wrap_to_it (pointer.2 - self.2) isize")]
    pub fn offset_from(&self, pointer: *const usize) -> isize {
        ptr_byte_offset(pointer, self.0)
    }

    /// Creates a new confidential memory address at given offset. Error is returned if the resulting address exceeds
    /// the upper boundary.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the address at given offset is still within the confidential memory region.
    // TODO: can we require the offset to be a multiple of usize? (woz: yes we can)
    #[rr::only_spec]
    #[rr::params("MEMORY_CONFIG")]
    /// Precondition: The global memory layout is initialized.
    #[rr::requires(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
    #[rr::ok]
    /// Precondition: The offset address is in the given range.
    #[rr::requires("self.2 + offset_in_bytes < upper_bound.2")]
    /// Precondition: The maximum (and thus the offset address) is in the confidential memory range.
    #[rr::requires("upper_bound.2 < MEMORY_CONFIG.(conf_end).2")]
    /// Postcondition: The offset pointer is in the confidential memory range.
    #[rr::ensures("ret = self +ₗ offset_in_bytes")]
    pub fn add(&self, offset_in_bytes: usize, upper_bound: *const usize) -> Result<ConfidentialMemoryAddress, Error> {
        let pointer = ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(|_| Error::AddressNotInConfidentialMemory())?;
        Ok(ConfidentialMemoryAddress(pointer))
    }

    /// Reads usize-sized sequence of bytes from the confidential memory region.
    /// # Safety
    ///
    /// Caller must ensure that the pointer is not used by two threads simultaneously and that it is correctly aligned for usize.
    /// See `ptr::read_volatile` for safety concerns
    #[rr::params("z", "lft_el")]
    #[rr::unsafe_elctx("[ϝ ⊑ₑ lft_el]")]
    #[rr::requires(#iris "self ◁ₗ[π, Shared lft_el] #z @ ◁ int usize")]
    #[rr::returns("z")]
    pub unsafe fn read_volatile<'a>(&'a self) -> usize {
        self.0.read_volatile()
    }

    /// Writes usize-sized sequence of bytes to the confidential memory region.
    /// # Safety
    ///
    /// Caller must ensure that the pointer is not used by two threads simultaneously and that it is correctly aligned for usize.
    /// See `ptr::write_volatile` for safety concerns
    #[rr::params("z")]
    #[rr::requires(#type "self" : "z" @ "int usize")]
    #[rr::ensures(#type "self" : "value" @ "int usize")]
    pub unsafe fn write_volatile(&self, value: usize) {
        self.0.write_volatile(value);
    }
}
