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

/// These wrappers serve as a temporary workaround until RefinedRust supports unsized types and in
/// particular slices: the indexing and iteration methods on `Vec` work by dereferencing to slices,
/// which currently are not supported by RefinedRust.
/// For now, we thus create wrappers for these methods to which we can attach RefinedRust
/// specifications.
mod rr_wrappers {
    use alloc::vec::Vec;

    #[rr::only_spec]
    #[rr::requires("index < length x.cur")]
    #[rr::exists("γi")]
    #[rr::returns("(x.cur !!! Z.to_nat index, γi)")]
    #[rr::observe("x.ghost": "<[Z.to_nat index := PlaceGhost γi]> (<$#> x.cur)")]
    pub fn vec_index_mut<T>(x: &mut Vec<T>, index: usize) -> &mut T {
        &mut x[index]
    }

    #[rr::only_spec]
    #[rr::requires("index < length x")]
    #[rr::returns("x !!! Z.to_nat index")]
    pub fn vec_index<T>(x: &Vec<T>, index: usize) -> &T {
        &x[index]
    }

    #[rr::only_spec]
    #[rr::returns("x")]
    pub fn vec_iter<T>(x: &Vec<T>) -> core::slice::Iter<'_, T> {
        x.iter()
    }

    #[rr::only_spec]
    #[rr::exists("γs")]
    #[rr::ensures("length γs = length x.cur")]
    #[rr::observe("x.ghost": "(PlaceGhost <$> γs) : list (place_rfn {rt_of T})")]
    #[rr::returns("zip x.cur γs")]
    pub fn vec_iter_mut<T>(x: &mut Vec<T>) -> core::slice::IterMut<'_, T> {
        x.iter_mut()
    }

}
