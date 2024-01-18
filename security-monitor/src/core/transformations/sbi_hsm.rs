// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStart {
    pub confidential_hart_id: usize,
    pub boot_code_address: usize,
    pub blob: usize,
}

impl SbiHsmHartStart {
    pub fn new(confidential_hart_id: usize, boot_code_address: usize, blob: usize) -> Self {
        Self { confidential_hart_id, boot_code_address, blob }
    }
}
