// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ConfidentialVmId;

#[derive(PartialEq)]
pub struct ResumeRequest {
    confidential_vm_id: ConfidentialVmId,
    confidential_hart_id: usize,
}

impl ResumeRequest {
    pub fn new(confidential_vm_id: usize, confidential_hart_id: usize) -> Self {
        let confidential_vm_id = ConfidentialVmId::new(confidential_vm_id);
        Self { confidential_vm_id, confidential_hart_id }
    }

    pub fn confidential_vm_id(&self) -> ConfidentialVmId {
        self.confidential_vm_id
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_id
    }
}
