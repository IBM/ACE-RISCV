// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use share_request::SharePageRequest;
pub use share_result::SharePageResult;
pub use unshare_request::UnsharePageRequest;

mod share_request;
mod share_result;
mod unshare_request;
