// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
use alloc::vec::Vec;
use core::ops::Range;

pub const MAX_NUMBER_OF_REGISTER_LENGTH: usize = 32;
const NUMBER_OF_VALUES_IN_REGISTER: usize = MAX_NUMBER_OF_REGISTER_LENGTH >> 3;
const NUMBER_OF_VECTOR_REGISTERS: usize = 32;

#[repr(C)]
pub struct VectorRegister(pub [u64; NUMBER_OF_VALUES_IN_REGISTER]);

#[repr(C)]
pub struct VectorRegisters(pub [usize; NUMBER_OF_VECTOR_REGISTERS]);
