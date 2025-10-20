// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]
#![feature(
    pointer_is_aligned_to,
    // used for formal verification framework (RefinedRust annotations)
    register_tool,
    custom_inner_attributes,
    stmt_expr_attributes,
)]
// RefinedRust configuration
#![register_tool(rr)]
#![rr::coq_prefix("sm")]
#![rr::include("stdlib")]
#![rr::include("pointers_utility")]

extern crate alloc;

#[macro_use]
mod debug;
mod confidential_flow;
mod core;
mod error;
mod non_confidential_flow;
