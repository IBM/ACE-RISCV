// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ConfidentialVmId;

#[derive(PartialEq)]
pub struct TerminateRequest {
    confidential_vm_id: ConfidentialVmId,
}

impl TerminateRequest {
    pub fn new(confidential_vm_id: usize) -> Self {
        Self { confidential_vm_id: ConfidentialVmId::new(confidential_vm_id) }
    }

    pub fn confidential_vm_id(&self) -> ConfidentialVmId {
        self.confidential_vm_id
    }
}
