// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[repr(usize)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PageSize {
    Size4KiB = 8 * 512,
    Size2MiB = 8 * 512 * 512,
    Size1GiB = 8 * 512 * 512 * 512,
    Size512GiB = 8 * 512 * 512 * 512 * 512,
    Size128TiB = 8 * 512 * 512 * 512 * 512 * 256,
}

impl PageSize {
    pub fn in_bytes(&self) -> usize {
        *self as usize
    }

    pub fn smaller(&self) -> Option<PageSize> {
        match self {
            PageSize::Size128TiB => Some(PageSize::Size512GiB),
            PageSize::Size512GiB => Some(PageSize::Size1GiB),
            PageSize::Size1GiB => Some(PageSize::Size2MiB),
            PageSize::Size2MiB => Some(PageSize::Size4KiB),
            PageSize::Size4KiB => None,
        }
    }

    pub fn larger(&self) -> Option<PageSize> {
        match self {
            PageSize::Size128TiB => None,
            PageSize::Size512GiB => Some(PageSize::Size128TiB),
            PageSize::Size1GiB => Some(PageSize::Size512GiB),
            PageSize::Size2MiB => Some(PageSize::Size1GiB),
            PageSize::Size4KiB => Some(PageSize::Size2MiB),
        }
    }

    pub fn smallest() -> PageSize {
        PageSize::Size4KiB
    }
}
