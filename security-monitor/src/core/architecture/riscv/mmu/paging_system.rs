// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::mmu::page_table_level::PageTableLevel;
use crate::core::architecture::mmu::HgatpMode;
use crate::core::architecture::PageSize;
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;

// TODO: add more 2nd-level paging systems corresponding to 3 and 4 level page
// tables.
#[derive(Debug, Copy, Clone)]
pub enum PagingSystem {
    Sv57x4,
}

impl PagingSystem {
    pub fn from(mode: &HgatpMode) -> Option<Self> {
        match mode {
            HgatpMode::Sv57x4 => Some(PagingSystem::Sv57x4),
        }
    }

    pub fn hgatp_mode(&self) -> HgatpMode {
        match self {
            Self::Sv57x4 => HgatpMode::Sv57x4,
        }
    }

    pub fn levels(&self) -> PageTableLevel {
        match self {
            PagingSystem::Sv57x4 => PageTableLevel::Level5,
        }
    }

    pub fn memory_page_size(&self, level: PageTableLevel) -> PageSize {
        match self {
            PagingSystem::Sv57x4 => match level {
                PageTableLevel::Level5 => PageSize::Size16KiB,
                _ => PageSize::Size4KiB,
            },
        }
    }

    // returns the size of the entry in bytes
    pub fn entry_size(&self) -> usize {
        match self {
            PagingSystem::Sv57x4 => 8,
        }
    }

    pub fn vpn(&self, virtual_address: &ConfidentialVmPhysicalAddress, level: PageTableLevel) -> usize {
        match self {
            PagingSystem::Sv57x4 => match level {
                PageTableLevel::Level5 => (virtual_address.usize() >> 48) & 0x3ff,
                PageTableLevel::Level4 => (virtual_address.usize() >> 39) & 0x1ff,
                PageTableLevel::Level3 => (virtual_address.usize() >> 30) & 0x1ff,
                PageTableLevel::Level2 => (virtual_address.usize() >> 21) & 0x1ff,
                PageTableLevel::Level1 => (virtual_address.usize() >> 12) & 0x1ff,
            },
        }
    }

    pub fn page_offset(&self, virtual_address: &ConfidentialVmPhysicalAddress, level: PageTableLevel) -> usize {
        let vpn_bits_mask = match self {
            PagingSystem::Sv57x4 => match level {
                PageTableLevel::Level5 => 0xfffffffff << 12,
                PageTableLevel::Level4 => 0x7ffffff << 12,
                PageTableLevel::Level3 => 0x3ffff << 12,
                PageTableLevel::Level2 => 0x1ff << 12,
                PageTableLevel::Level1 => 0 << 12,
            },
        };
        let vpn_to_rewrite = virtual_address.usize() & vpn_bits_mask;
        let page_offset = virtual_address.usize() & 0xfff;
        vpn_to_rewrite | page_offset
    }

    pub fn data_page_size(&self, level: PageTableLevel) -> PageSize {
        match level {
            PageTableLevel::Level5 => PageSize::Size128TiB,
            PageTableLevel::Level4 => PageSize::Size512GiB,
            PageTableLevel::Level3 => PageSize::Size1GiB,
            PageTableLevel::Level2 => PageSize::Size2MiB,
            PageTableLevel::Level1 => PageSize::Size4KiB,
        }
    }
}
