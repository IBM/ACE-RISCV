// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;

pub const KVM_ACE_EXTID: usize = 0x509999;

pub fn load_all_pages() -> Result<usize, Error> {
    super::ecall(KVM_ACE_EXTID, 0, 0, 0, 0, 0, 0).map_err(|_| Error::LoadAllPagesFailed())
}
