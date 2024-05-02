// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;

const COVH_EXTID: usize = 0x434F5648;
const COVG_EXTID: usize = 0x434F5647;

const PROMOTE_FID: usize = 21;
const SHARE_PAGE_FID: usize = 2;

pub fn esm(fdt_addr: usize) -> Result<usize, Error> {
    super::ecall(COVH_EXTID, PROMOTE_FID, fdt_addr, 0, 0, 0, 0).map_err(|_| Error::EsmError())
}

pub fn share_page(paddr: usize, number_of_pages: usize) -> Result<usize, Error> {
    super::ecall(COVG_EXTID, SHARE_PAGE_FID, paddr, number_of_pages, 0, 0, 0).map_err(|_| Error::SharePageError())
}
