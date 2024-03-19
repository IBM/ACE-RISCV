// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStart {
    confidential_hart_id: usize,
    start_address: usize,
    opaque: usize,
}

impl SbiHsmHartStart {
    pub fn new(confidential_hart_id: usize, start_address: usize, opaque: usize) -> Self {
        Self { confidential_hart_id, start_address, opaque }
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_id
    }

    pub fn start_address(&self) -> usize {
        self.start_address
    }

    pub fn opaque(&self) -> usize {
        self.opaque
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartSuspend {
    suspend_type: usize,
    resume_address: usize,
    opaque: usize,
}

impl SbiHsmHartSuspend {
    pub fn new(suspend_type: usize, resume_address: usize, opaque: usize) -> Self {
        Self { suspend_type, resume_address, opaque }
    }

    pub fn suspend_type(&self) -> usize {
        self.suspend_type
    }

    pub fn resume_address(&self) -> usize {
        self.resume_address
    }

    pub fn opaque(&self) -> usize {
        self.opaque
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStatus {
    confidential_hart_id: usize,
}

impl SbiHsmHartStatus {
    pub fn new(confidential_hart_id: usize) -> Self {
        Self { confidential_hart_id }
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_id
    }
}
