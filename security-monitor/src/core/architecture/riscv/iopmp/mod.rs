// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;

pub fn protect_confidential_memory_from_io_devices(
    _confidential_memory_start: usize, _confidential_memory_end: usize,
) -> Result<(), Error> {
    // TODO: implement IOPMP configuration
    Ok(())
}
