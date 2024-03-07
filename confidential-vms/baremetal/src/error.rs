// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use thiserror_no_std::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Virtio Error")]
    VirtioError(),
    #[error("ESM error")]
    EsmError(),
    #[error("Share page error")]
    SharePageError(),
    #[error("Load all pages failed")]
    LoadAllPagesFailed(),
}
