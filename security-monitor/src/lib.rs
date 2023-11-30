// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]
#![feature(
    // used for meaningful panic code
    panic_info_message,
    // used for calculating offsets for assembly
    asm_const,
    // const_mut_ref for LinkedList implementation used in the heap allocator
    const_mut_refs,
    pointer_is_aligned,
    // pointer_is_aligned_to,
    result_option_inspect,
    pointer_byte_offsets,
    // used for formal verification framework (RefinedRust annotations)
    register_tool,
    custom_inner_attributes,
)]
// RefinedRust configuration
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
