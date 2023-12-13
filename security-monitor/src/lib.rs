// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]
#![crate_type = "staticlib"]
// used for meaningful panic code
#![feature(panic_info_message)]
// used for calculating offsets for assembly
#![feature(asm_const)]
// const_mut_ref for LinkedList implementation used in the heap allocator
#![feature(const_mut_refs)]
// #![feature(const_refs_to_cell)]
// used to run closure on Err(). Simplifies syntax and can be removed in future
#![feature(result_option_inspect)]
// used for convenience for calculating offsets between *usize pointers as bytes
#![feature(pointer_byte_offsets)]
#![feature(pointer_is_aligned)]
// used for RefinedRust annotations
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

// extern creates
extern crate alloc;
// pub use declarations
// use declarations
// pub mod declarations
// mod declarations
#[macro_use]
mod debug;
mod confidential_flow;
mod core;
mod error;
mod non_confidential_flow;
