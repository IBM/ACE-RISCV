// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#[derive(PartialEq)]
pub struct SharePageResult {
    response_code: usize,
    hypervisor_page_address: usize,
}

impl SharePageResult {
    pub fn new(response_code: usize, hypervisor_page_address: usize) -> Self {
        Self { response_code, hypervisor_page_address }
    }

    pub fn is_error(&self) -> bool {
        self.response_code > 0
    }

    pub fn response_code(&self) -> usize {
        self.response_code
    }

    pub fn hypervisor_page_address(&self) -> usize {
        self.hypervisor_page_address
    }
}
