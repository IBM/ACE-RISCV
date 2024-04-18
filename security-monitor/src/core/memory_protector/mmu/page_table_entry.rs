// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_protector::mmu::page_table::PageTable;
use crate::core::memory_protector::SharedPage;
use crate::core::page_allocator::{Allocated, Page};
use alloc::boxed::Box;

#[rr::refined_by("page_table_entry")]
pub(super) enum PageTableEntry {
    // node
    #[rr::pattern("PointerToNextPageTable" $ "next", "conf")]
    #[rr::refinement("-[ #(#next); #conf]")]
    PointerToNextPageTable(Box<PageTable>, PageTableConfiguration),
    // leaf
    #[rr::pattern("PageWithConfidentialVmData" $ "p", "conf", "perm")]
    #[rr::refinement("-[ #(#p); #conf; #perm]")]
    PageWithConfidentialVmData(Box<Page<Allocated>>, PageTableConfiguration, PageTablePermission),
    #[rr::pattern("PageSharedWithHypervisor" $ "sp", "conf", "perm")]
    #[rr::refinement("-[ #sp; #conf; #perm]")]
    PageSharedWithHypervisor(SharedPage, PageTableConfiguration, PageTablePermission),
    // this is an unmapped page
    #[rr::pattern("UnmappedPage")]
    UnmappedPage,
}

impl PageTableEntry {
    pub fn encode(&self) -> usize {
        match self {
            PageTableEntry::PointerToNextPageTable(page_table, configuration) => {
                PageTableBits::Valid.mask() | PageTableAddress::encode(page_table.address()) | configuration.encode()
            }
            PageTableEntry::PageWithConfidentialVmData(page, configuration, permissions) => {
                PageTableBits::Valid.mask() | PageTableAddress::encode(page.start_address()) | configuration.encode() | permissions.encode()
            }
            PageTableEntry::PageSharedWithHypervisor(shared_page, configuration, permissions) => {
                PageTableBits::Valid.mask()
                    | PageTableAddress::encode(shared_page.hypervisor_address.usize())
                    | configuration.encode()
                    | permissions.encode()
            }
            PageTableEntry::UnmappedPage => 0,
        }
    }
}

#[derive(Copy, Clone)]
#[rr::refined_by("pte_flags_bits")]
pub(super) enum PageTableBits {
    #[rr::pattern("PTValid")]
    Valid = 0,
    #[rr::pattern("PTRead")]
    Read = 1,
    #[rr::pattern("PTWrite")]
    Write = 2,
    #[rr::pattern("PTExecute")]
    Execute = 3,
    #[rr::pattern("PTUser")]
    User = 4,
    #[rr::pattern("PTGlobal")]
    Global = 5,
    #[rr::pattern("PTAccessed")]
    Accessed = 6,
    #[rr::pattern("PTDirty")]
    Dirty = 7,
}

impl PageTableBits {
    pub const fn mask(&self) -> usize {
        1 << (*self as usize)
    }

    pub const fn is_set(&self, raw_entry: usize) -> bool {
        raw_entry & self.mask() != 0
    }

    pub const fn is_valid(raw_entry: usize) -> bool {
        Self::Valid.is_set(raw_entry)
    }

    pub const fn is_leaf(raw_entry: usize) -> bool {
        Self::Read.is_set(raw_entry) || Self::Write.is_set(raw_entry) || Self::Execute.is_set(raw_entry)
    }
}

pub(super) struct PageTableAddress();

impl PageTableAddress {
    const CONFIGURATION_BIT_MASK: usize = 0x3ff; // first 10 bits
    const ADDRESS_SHIFT: usize = 2;

    pub const fn decode(raw_entry: usize) -> *mut usize {
        ((raw_entry & !Self::CONFIGURATION_BIT_MASK) << Self::ADDRESS_SHIFT) as *mut usize
    }

    pub fn encode(address: usize) -> usize {
        address >> Self::ADDRESS_SHIFT
    }
}

#[rr::refined_by("x" : "page_table_permission")]
pub(super) struct PageTablePermission {
    #[rr::field("x.(ptp_can_read)")]
    can_read: bool,
    #[rr::field("x.(ptp_can_write)")]
    can_write: bool,
    #[rr::field("x.(ptp_can_execute)")]
    can_execute: bool,
}

impl PageTablePermission {
    pub fn shared_page_permission() -> Self {
        Self { can_read: true, can_write: true, can_execute: false }
    }

    pub fn decode(raw_entry: usize) -> Self {
        let can_read = PageTableBits::Read.is_set(raw_entry);
        let can_write = PageTableBits::Write.is_set(raw_entry);
        let can_execute = PageTableBits::Execute.is_set(raw_entry);
        Self { can_read, can_write, can_execute }
    }

    pub fn encode(&self) -> usize {
        let mut encoded_value = 0;
        if self.can_read {
            encoded_value = encoded_value | PageTableBits::Read.mask();
        }
        if self.can_write {
            encoded_value = encoded_value | PageTableBits::Write.mask();
        }
        if self.can_execute {
            encoded_value = encoded_value | PageTableBits::Execute.mask();
        }
        encoded_value
    }
}

#[rr::refined_by("x" : "page_table_config")]
pub(super) struct PageTableConfiguration {
    #[rr::field("x.(pt_accessible_to_user)")]
    is_accessible_to_user: bool,
    #[rr::field("x.(pt_was_accessed)")]
    was_accessed: bool,
    #[rr::field("x.(pt_is_global_mapping)")]
    is_global_mapping: bool,
    #[rr::field("x.(pt_is_dirty)")]
    is_dirty: bool,
}

impl PageTableConfiguration {
    pub fn empty() -> Self {
        Self { is_accessible_to_user: false, was_accessed: false, is_global_mapping: false, is_dirty: false }
    }

    pub fn shared_page_configuration() -> Self {
        Self { is_accessible_to_user: true, was_accessed: true, is_global_mapping: false, is_dirty: true }
    }

    pub fn decode(raw_entry: usize) -> Self {
        let is_accessible_to_user = PageTableBits::User.is_set(raw_entry);
        let was_accessed = PageTableBits::Accessed.is_set(raw_entry);
        let is_global_mapping = PageTableBits::Global.is_set(raw_entry);
        let is_dirty = PageTableBits::Dirty.is_set(raw_entry);
        Self { is_accessible_to_user, was_accessed, is_global_mapping, is_dirty }
    }

    pub fn encode(&self) -> usize {
        let mut encoded_value = 0;
        if self.is_accessible_to_user {
            encoded_value = encoded_value | PageTableBits::User.mask();
        }
        if self.was_accessed {
            encoded_value = encoded_value | PageTableBits::Accessed.mask();
        }
        if self.is_global_mapping {
            encoded_value = encoded_value | PageTableBits::Global.mask();
        }
        if self.is_dirty {
            encoded_value = encoded_value | PageTableBits::Dirty.mask();
        }
        encoded_value
    }
}
