// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::transformations::SbiRequest;

pub struct SbiVmRequest {
    sbi_request: SbiRequest,
}

impl SbiVmRequest {
    pub fn from_hart_state(hart_state: &HartArchitecturalState) -> Self {
        let sbi_request = SbiRequest::new(
            hart_state.gpr(GeneralPurposeRegister::a7),
            hart_state.gpr(GeneralPurposeRegister::a6),
            hart_state.gpr(GeneralPurposeRegister::a0),
            hart_state.gpr(GeneralPurposeRegister::a1),
            hart_state.gpr(GeneralPurposeRegister::a2),
            hart_state.gpr(GeneralPurposeRegister::a3),
            hart_state.gpr(GeneralPurposeRegister::a4),
            hart_state.gpr(GeneralPurposeRegister::a5),
        );
        Self { sbi_request }
    }

    pub fn sbi_request(&self) -> &SbiRequest {
        &self.sbi_request
    }
}
