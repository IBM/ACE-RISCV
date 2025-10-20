// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![rr::import("ace.theories.page_table", "page_table")]
use super::specification::*;
use crate::core::architecture::SharedPage;
use crate::core::architecture::mmu::page_table::PageTable;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::core::page_allocator::{Allocated, Page};
use crate::error::Error;
use alloc::boxed::Box;

/// Logical page table entry contains variants specific to the security monitor architecture. These new variants distinguish among certain
/// types (e.g., shared page, confidential data page) that are not covered by the general RISC-V specification.
#[rr::refined_by("logical_page_table_entry")]
pub(super) enum LogicalPageTableEntry {
    #[rr::pattern("PointerToNextPageTable" $ "next", "conf")]
    #[rr::refinement("-[ #(#next); #conf]")]
    PointerToNextPageTable(Box<PageTable>),
    #[rr::pattern("PageWithConfidentialVmData" $ "p", "conf", "perm")]
    #[rr::refinement("-[ #(#p); #conf; #perm]")]
    PageWithConfidentialVmData(Box<Page<Allocated>>),
    #[rr::pattern("PageSharedWithHypervisor" $ "sp", "conf", "perm")]
    #[rr::refinement("-[ #sp; #conf; #perm]")]
    PageSharedWithHypervisor(SharedPage),
    #[rr::pattern("UnmappedPage")]
    NotMapped,
}

impl LogicalPageTableEntry {
    pub fn serialize(&self) -> usize {
        match self {
            Self::PointerToNextPageTable(page_table) => {
                page_table.address() >> ADDRESS_SHIFT
                    | PAGE_TABLE_ENTRY_EMPTY_CONF
                    | PAGE_TABLE_ENTRY_NO_PERMISSIONS
                    | PAGE_TABLE_ENTRY_VALID_MASK
            }
            Self::PageWithConfidentialVmData(page) => {
                page.start_address() >> ADDRESS_SHIFT
                    | PAGE_TABLE_ENTRY_UAD_CONF_MASK
                    | PAGE_TABLE_ENTRY_RWX_PERMISSIONS
                    | PAGE_TABLE_ENTRY_VALID_MASK
            }
            Self::PageSharedWithHypervisor(shared_page) => {
                shared_page.hypervisor_address.usize() >> ADDRESS_SHIFT
                    | PAGE_TABLE_ENTRY_UAD_CONF_MASK
                    | PAGE_TABLE_ENTRY_RW_PERMISSIONS
                    | PAGE_TABLE_ENTRY_VALID_MASK
            }
            Self::NotMapped => PAGE_TABLE_ENTRY_NOT_MAPPED,
        }
    }
}

/// Page table entry corresponds to entires defined by the RISC-V spec.
#[rr::refined_by("page_table_entry")]
pub(super) enum PageTableEntry {
    #[rr::pattern("UnmappedPTE")]
    NotMapped,
    #[rr::pattern("NextPTE" $ "p")]
    #[rr::refinement("-[ #p]")]
    PointerToNextPageTable(*mut usize),
    #[rr::pattern("DataPTE" $ "p")]
    #[rr::refinement("-[ #p]")]
    PointerToDataPage(*mut usize),
}

impl PageTableEntry {
    pub fn deserialize(serialized_entry: usize) -> Self {
        match serialized_entry & PAGE_TABLE_ENTRY_TYPE_MASK {
            PAGE_TABLE_ENTRY_NOT_MAPPED => Self::NotMapped,
            PAGE_TABLE_ENTRY_POINTER => Self::PointerToNextPageTable(Self::decode_pointer(serialized_entry)),
            _ => Self::PointerToDataPage(Self::decode_pointer(serialized_entry)),
        }
    }

    /// Decodes a raw pointer from the page table entry. It is up to the user to decide how to deal with this pointer and check if it is
    /// valid and is in confidential or non-confidential memory.
    pub fn decode_pointer(raw_entry: usize) -> *mut usize {
        // TODO: think how we can justify the integer-pointer cast
        ((raw_entry & !CONFIGURATION_BIT_MASK) << ADDRESS_SHIFT) as *mut usize
    }
}
