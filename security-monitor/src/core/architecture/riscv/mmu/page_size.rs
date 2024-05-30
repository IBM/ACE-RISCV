// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

// The order of page size in this enum must follow the increasing sizes of page to guarantee that the Ord/PartialOrd are correctly derived
// for the `PageSize`.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PageSize {
    Size4KiB,
    /// 16KiB page is used by G-stage root page table in RISC-V
    Size16KiB,
    Size2MiB,
    Size1GiB,
    Size512GiB,
    Size128TiB,
}

impl PageSize {
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

    pub fn largest() -> PageSize {
        PageSize::Size128TiB
    }

    pub fn smallest() -> PageSize {
        PageSize::Size4KiB
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_partial_order() {
        assert!(PageSize::Size4KiB < PageSize::Size16KiB);
        assert!(PageSize::Size16KiB < PageSize::Size2MiB);
        assert!(PageSize::Size2MiB < PageSize::Size1GiB);
        assert!(PageSize::Size1GiB < PageSize::Size512GiB);
        assert!(PageSize::Size512GiB < PageSize::Size128TiB);
    }

    #[test]
    fn check_smaller_pages_constant() {
        let smaller_pages = |p: PageSize| p.in_bytes() / p.smaller().unwrap().in_bytes();
        assert_eq!(PageSize::Size128TiB.number_of_smaller_pages(), smaller_pages(PageSize::Size128TiB));
        assert_eq!(PageSize::Size512GiB.number_of_smaller_pages(), smaller_pages(PageSize::Size512GiB));
        assert_eq!(PageSize::Size1GiB.number_of_smaller_pages(), smaller_pages(PageSize::Size1GiB));
        assert_eq!(PageSize::Size2MiB.number_of_smaller_pages(), smaller_pages(PageSize::Size2MiB));
        assert_eq!(PageSize::Size16KiB.number_of_smaller_pages(), smaller_pages(PageSize::Size16KiB));
        assert_eq!(PageSize::Size4KiB.number_of_smaller_pages(), 0);
    }
}
