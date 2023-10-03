// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use memory_address::{ConfidentialMemoryAddress, NonConfidentialMemoryAddress, CONFIDENTIAL_MEMORY_RANGE};
pub use memory_tracker::{MemoryTracker, MEMORY_TRACKER};
pub use page::{Allocated, Page, PageState, UnAllocated};
pub use shared_page::SharedPage;

mod memory_address;
mod memory_tracker;
mod page;
mod shared_page;
