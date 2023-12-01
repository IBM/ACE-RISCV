// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]
#![feature(pointer_byte_offsets)]

mod error;
use core::mem::size_of;
pub use crate::error::PointerError;

pub fn ptr_byte_offset(pointer1: *const usize, pointer2: *const usize) -> isize {
    (pointer1 as isize) - (pointer2 as isize)
}

pub fn ptr_align(pointer: *mut usize, align_in_bytes: usize, owned_region_end: *const usize) -> Result<*mut usize, PointerError> {
    let offset_to_align = pointer.align_offset(align_in_bytes) * size_of::<*mut usize>();
    ptr_byte_add_mut(pointer, offset_to_align, owned_region_end)
}

/// A safe variant of calculating the offset from a pointer. This function guarantees that
/// the returning pointer did not overflow and is within the owned memory region excluding
/// the one-past-the-end address. The returned pointer is guaranteed to be valid for accesses
/// of size one, if the original pointer is valid. Additional checks are required for making
/// larger memory accesses.
pub fn ptr_byte_add_mut(
    pointer: *mut usize, offset_in_bytes: usize, owned_region_end: *const usize,
) -> Result<*mut usize, PointerError> {
    let incremented_pointer = pointer.wrapping_byte_add(offset_in_bytes);
    // Safety: Check if the pointer is still within the owned region
    if (incremented_pointer as *const usize) >= owned_region_end {
        return Err(PointerError::Overflow);
    }
    // Safety: make sure the add operation did not overflow
    if offset_in_bytes > 0 && incremented_pointer <= pointer {
        return Err(PointerError::Overflow);
    }
    Ok(incremented_pointer)
}

pub fn ptr_byte_add(
    pointer: *const usize, offset_in_bytes: usize, owned_region_end: *const usize,
) -> Result<*const usize, PointerError> {
    Ok(ptr_byte_add_mut(pointer as *mut usize, offset_in_bytes, owned_region_end)?)
}
