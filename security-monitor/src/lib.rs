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
#![feature(pointer_is_aligned)]
#![feature(result_option_inspect)]
#![feature(pointer_byte_offsets)]
// used for RefinedRust annotations
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![rr::coq_prefix("ace")]

extern crate alloc;

#[macro_use]
mod debug;
mod confidential_flow;
mod core;
mod error;
mod non_confidential_flow;
