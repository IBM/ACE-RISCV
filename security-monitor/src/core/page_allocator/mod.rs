// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use allocator::PageAllocator;
pub use page::{Allocated, Page, UnAllocated};

mod allocator;
mod page;
