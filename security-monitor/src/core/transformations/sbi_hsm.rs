// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStart {
    pub confidential_hart_id: usize,
    pub start_address: usize,
    pub opaque: usize,
}

impl SbiHsmHartStart {
    pub fn new(confidential_hart_id: usize, start_address: usize, opaque: usize) -> Self {
        Self { confidential_hart_id, start_address, opaque }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartSuspend {
    pub suspend_type: usize,
    pub resume_address: usize,
    pub opaque: usize,
}

impl SbiHsmHartSuspend {
    pub fn new(suspend_type: usize, resume_address: usize, opaque: usize) -> Self {
        Self { suspend_type, resume_address, opaque }
    }
}
