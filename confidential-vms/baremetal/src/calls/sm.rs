// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;

const ACE_EXTID: usize = 0x510000;

const ACE_ESM_FID: usize = 1000;
const ACE_SHARE_PAGE_FID: usize = 2000;

pub fn esm() -> Result<usize, Error> {
    super::ecall(ACE_EXTID, ACE_ESM_FID, 0, 0, 0, 0, 0).map_err(|_| Error::EsmError())
}

pub fn share_page(paddr: usize, number_of_pages: usize) -> Result<usize, Error> {
    super::ecall(ACE_EXTID, ACE_SHARE_PAGE_FID, paddr, number_of_pages, 0, 0, 0).map_err(|_| Error::SharePageError())
}

