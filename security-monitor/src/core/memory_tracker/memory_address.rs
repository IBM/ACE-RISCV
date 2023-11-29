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

#[repr(transparent)]
#[derive(Debug)]
pub struct NonConfidentialMemoryAddress(usize);

impl NonConfidentialMemoryAddress {
    pub fn new(address: usize) -> Result<Self, Error> {
        use crate::error::NOT_INITIALIZED_CONFIDENTIAL_MEMORY;
        match CONFIDENTIAL_MEMORY_RANGE.get().expect(NOT_INITIALIZED_CONFIDENTIAL_MEMORY).contains(&address) {
            true => Err(Error::MemoryAccessAuthorization()),
            false => Ok(Self(address)),
        }
    }

    pub fn usize(&self) -> usize {
        self.0
    }
}
