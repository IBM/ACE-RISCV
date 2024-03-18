// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use page::{Allocated, Page, UnAllocated};
pub use page_allocator::PageAllocator;

mod page;
mod page_allocator;
