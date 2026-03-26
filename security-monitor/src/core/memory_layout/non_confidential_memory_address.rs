// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::MemoryLayout;
use crate::error::Error;
use pointers_utility::ptr_byte_add_mut;

/// The wrapper over a raw pointer that is guaranteed to be an address located in the non-confidential memory region.
#[repr(transparent)]
#[derive(Debug)]
/// Model: The memory address is represented by the location in memory.
#[rr::refined_by("l" : "loc")]
/// We require the ghost state for the global memory layout to be available.
#[rr::context("onceG Σ memory_layout")]
/// Invariant: The global memory layout has been initialized.
#[rr::exists("MEMORY_CONFIG")]
#[rr::invariant(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
/// Invariant: The address is in non-confidential memory.
#[rr::invariant("(MEMORY_CONFIG.(non_conf_start).(loc_a) ≤ l.(loc_a) < MEMORY_CONFIG.(non_conf_end).(loc_a))%Z")]
pub struct NonConfidentialMemoryAddress(#[rr::field("l")] *mut usize);

#[rr::context("onceG Σ memory_layout")]
impl NonConfidentialMemoryAddress {
    /// Constructs an address in a non-confidential memory. Returns error if the address is outside non-confidential
    /// memory.
    #[rr::params("bounds")]
    /// Precondition: The global memory layout has been initialized.
    #[rr::requires(#iris "once_initialized π \"MEMORY_LAYOUT\" (Some bounds)")]
    #[rr::ok]
    /// Precondition: The location is in non-confidential memory.
    #[rr::requires("bounds.(non_conf_start).(loc_a) ≤ address.(loc_a) < bounds.(non_conf_end).(loc_a)")]
    /// Postcondition: The non-confidential memory address is correctly initialized.
    #[rr::ensures("ret = address")]
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
    #[rr::params("MEMORY_CONFIG" : "memory_layout")]
    /// Precondition: The global memory layout is initialized.
    #[rr::requires(#iris "once_initialized π \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
    #[rr::ok]
    /// Precondition: The offset address is in the given range.
    #[rr::requires("self.(loc_a) + offset_in_bytes < upper_bound.(loc_a)")]
    /// Precondition: The maximum (and thus the offset address) is in the non-confidential memory range.
    #[rr::requires("upper_bound.(loc_a) ≤ MEMORY_CONFIG.(non_conf_end).(loc_a)")]
    /// Postcondition: The offset pointer is in the non-confidential memory range.
    #[rr::ensures("ret = self +ₗ offset_in_bytes")]
    pub unsafe fn add(&self, offset_in_bytes: usize, upper_bound: *const usize) -> Result<NonConfidentialMemoryAddress, Error> {
        let memory_layout = MemoryLayout::read();
        ensure!(upper_bound <= memory_layout.non_confidential_memory_end, Error::AddressNotInNonConfidentialMemory())?;
        let pointer = ptr_byte_add_mut(self.0, offset_in_bytes, upper_bound).map_err(#[rr::verify] |_| Error::AddressNotInNonConfidentialMemory())?;
        Ok(NonConfidentialMemoryAddress(pointer))
    }

    /// Reads usize-sized sequence of bytes from the non-confidential memory region.
    ///
    /// # Safety
    ///
    /// We need to ensure the pointer is not used by two threads simultaneously. See `ptr::read_volatile` for safety
    /// concerns.
    #[rr::params("z", "lft_el")]
    #[rr::unsafe_elctx("[ϝ ⊑ₑ lft_el]")]
    #[rr::requires(#iris "self ◁ₗ[π, Shared lft_el] #z @ ◁ int usize")]
    #[rr::returns("z")]
    pub unsafe fn read(&self) -> usize {
        unsafe { self.0.read_volatile() }
    }

    /// Writes usize-sized sequence of bytes to the non-confidential memory region.
    ///
    /// # Safety
    ///
    /// We need to ensure the pointer is not used by two threads simultaneously. See `ptr::write_volatile` for safety
    /// concerns.
    #[rr::params("z")]
    #[rr::requires(#type "self" : "z" @ "int usize")]
    #[rr::ensures(#type "self" : "value" @ "int usize")]
    pub unsafe fn write(&self, value: usize) {
        unsafe { self.0.write_volatile(value) };
    }

    #[rr::returns("self")]
    pub fn as_ptr(&self) -> *const usize {
        self.0
    }

    #[rr::returns("self.(loc_a)")]
    pub fn usize(&self) -> usize {
        // TODO: check if we need to expose the pointer.
        self.0.addr()
    }
}
