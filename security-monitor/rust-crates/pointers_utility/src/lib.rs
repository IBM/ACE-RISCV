// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]
#![feature(pointer_byte_offsets)]

// used for RefinedRust annotations
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::coq_prefix("ace_ptr")]


mod error;
use core::mem::size_of;
pub use crate::error::PointerError;

/// Calculates the offset in bytes between two pointers. 
pub fn ptr_byte_offset(pointer1: *const usize, pointer2: *const usize) -> isize {
    (pointer1 as isize) - (pointer2 as isize)
}

/// Aligns the pointer to specific size while making sure that the aligned pointer
/// is still within the memory region owned by the original pointer. Check `ptr_byte_add_mut`
/// to learn about guarantees for the returned pointer.
pub fn ptr_align(pointer: *mut usize, align_in_bytes: usize, owned_region_end: *const usize) -> Result<*mut usize, PointerError> {
    let offset_to_align = pointer.align_offset(align_in_bytes) * size_of::<usize>();
    ptr_byte_add_mut(pointer, offset_to_align, owned_region_end)
}

/// Calculates the offset from a mutable raw pointer. This function guarantees that
/// the returning pointer did not overflow and is within the owned memory region excluding
/// the one-past-the-end address. The returned pointer is guaranteed to be valid for accesses
/// of size one, if the original pointer is valid. Additional checks are required for making
/// larger memory accesses.
#[rr::skip]
#[rr::params("l", "off", "lmax")]
#[rr::args("l", "off", "lmax")]
#[rr::requires("⌜l.2 + off < lmax.2⌝")]
#[rr::returns("Ok(l +ₗ off)")]
pub fn ptr_byte_add_mut(
    pointer: *mut usize, offset_in_bytes: usize, owned_region_end: *const usize,
) -> Result<*mut usize, PointerError> {
    let incremented_pointer = pointer.wrapping_byte_add(offset_in_bytes);
    // Safety: We check that the pointer is still within the owned region
    if (incremented_pointer as *const usize) >= owned_region_end {
        return Err(PointerError::Overflow);
    }
    // Safety: We check that the add operation did not overflow
    if offset_in_bytes > 0 && incremented_pointer <= pointer {
        return Err(PointerError::Overflow);
    }
    Ok(incremented_pointer)
}

/// Calculates the offset from a raw pointer. This function guarantees that
/// the returning pointer did not overflow and is within the owned memory region excluding
/// the one-past-the-end address. The returned pointer is guaranteed to be valid for accesses
/// of size one, if the original pointer is valid. Additional checks are required for making
/// larger memory accesses.
pub fn ptr_byte_add(
    pointer: *const usize, offset_in_bytes: usize, owned_region_end: *const usize,
) -> Result<*const usize, PointerError> {
    Ok(ptr_byte_add_mut(pointer as *mut usize, offset_in_bytes, owned_region_end)?)
}
