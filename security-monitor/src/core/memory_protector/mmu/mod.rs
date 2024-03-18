// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{Hgatp, CSR};
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::error::Error;

pub use page_size::PageSize;
pub use page_table::RootPageTable;
pub use paging_system::PagingSystem;
pub use shared_page::SharedPage;

mod page_size;
mod page_table;
mod page_table_entry;
mod page_table_memory;
mod paging_system;
mod shared_page;

pub fn copy_mmu_configuration_from_non_confidential_memory(hgatp: Hgatp) -> Result<RootPageTable, Error> {
    let paging_mode = hgatp.mode().ok_or_else(|| Error::UnsupportedPagingMode())?;
    let paging_system = PagingSystem::from(&paging_mode).ok_or_else(|| Error::UnsupportedPagingMode())?;
    let root_page_address = NonConfidentialMemoryAddress::new(hgatp.address() as *mut usize)?;
    let root_page_table = RootPageTable::copy_from_non_confidential_memory(root_page_address, paging_system)?;
    Ok(root_page_table)
}

pub fn enable_address_translation(hgatp: usize) {
    // Enable MMU for HS,VS,VS,U modes. It is safe to invoke below code because we have access to this register (run in the M-mode) and
    // hgatp is the content of the HGATP register calculated by the security monitor when recreating page tables of a confidential virtual
    // machine that will get executed.
    CSR.hgatp.set(hgatp);
}
