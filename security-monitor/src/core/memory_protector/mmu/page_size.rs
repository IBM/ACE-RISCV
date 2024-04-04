// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![rr::import("ace.theories.page", "page_extra")]
#![rr::include("option")]

// The order of page size in this enum must follow the increasing sizes of
// page to guarantee that the Ord/PartialOrd are correctly derived for the `PageSize`.
// TODO: add unit tests to make sure PageSize can be correctly compared between each other.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[rr::refined_by("page_size")]
pub enum PageSize {
    #[rr::pattern("Size4KiB")]
    Size4KiB,
    /// 16KiB page is used by G-stage root page table in RISC-V
    #[rr::pattern("Size16MiB")]
    Size16KiB,
    #[rr::pattern("Size2MiB")]
    Size2MiB,
    #[rr::pattern("Size1GiB")]
    Size1GiB,
    #[rr::pattern("Size512GiB")]
    Size512GiB,
    #[rr::pattern("Size128TiB")]
    Size128TiB,
}

impl PageSize {
    // Usually there are 512 pages of size x that can fit in a single page of size y, where y is next page size larger than x (e.g., 2MiB
    // and 4KiB).
    pub const TYPICAL_NUMBER_OF_PAGES_INSIDE_LARGER_PAGE: usize = 512;

    #[rr::trust_me]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("page_size_in_bytes_Z x")]
    pub fn in_bytes(&self) -> usize {
        match self {
            PageSize::Size128TiB => 8 * 512 * 512 * 512 * 512 * 256,
            PageSize::Size512GiB => 8 * 512 * 512 * 512 * 512,
            PageSize::Size1GiB => 8 * 512 * 512 * 512,
            PageSize::Size2MiB => 8 * 512 * 512,
            PageSize::Size16KiB => 4 * 8 * 512,
            PageSize::Size4KiB => 8 * 512,
        }
    }

    #[rr::trust_me]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("<#>@{option} page_size_smaller x")]
    pub fn smaller(&self) -> Option<PageSize> {
        match self {
            PageSize::Size128TiB => Some(PageSize::Size512GiB),
            PageSize::Size512GiB => Some(PageSize::Size1GiB),
            PageSize::Size1GiB => Some(PageSize::Size2MiB),
            PageSize::Size2MiB => Some(PageSize::Size16KiB),
            PageSize::Size16KiB => Some(PageSize::Size4KiB),
            PageSize::Size4KiB => None,
        }
    }

    #[rr::trust_me]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("<#>@{option} page_size_larger x")]
    pub fn larger(&self) -> Option<PageSize> {
        match self {
            PageSize::Size128TiB => None,
            PageSize::Size512GiB => Some(PageSize::Size128TiB),
            PageSize::Size1GiB => Some(PageSize::Size512GiB),
            PageSize::Size2MiB => Some(PageSize::Size1GiB),
            PageSize::Size16KiB => Some(PageSize::Size2MiB),
            PageSize::Size4KiB => Some(PageSize::Size16KiB),
        }
    }

    pub fn number_of_smaller_pages(&self) -> usize {
        match self {
            PageSize::Size128TiB => 256,
            PageSize::Size512GiB => 512,
            PageSize::Size1GiB => 512,
            PageSize::Size2MiB => 128,
            PageSize::Size16KiB => 4,
            PageSize::Size4KiB => 0,
        }
    }

    #[rr::returns("Size128TiB")]
    pub fn largest() -> PageSize {
        PageSize::Size128TiB
    }

    #[rr::returns("Size4KiB")]
    pub fn smallest() -> PageSize {
        PageSize::Size4KiB
    }
}
