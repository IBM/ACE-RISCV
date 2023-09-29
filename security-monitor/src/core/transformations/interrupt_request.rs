// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub struct InterruptRequest {
    code: usize,
}

impl InterruptRequest {
    pub fn new(code: usize) -> Self {
        Self { code }
    }

    pub fn code(&self) -> usize {
        self.code
    }
}
