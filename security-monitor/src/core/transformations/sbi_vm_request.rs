// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GpRegister, HartArchitecturalState};
use crate::core::transformations::SbiRequest;

pub struct SbiVmRequest {
    sbi_request: SbiRequest,
}

impl SbiVmRequest {
    pub fn from_hart_state(hart_state: &HartArchitecturalState) -> Self {
        let sbi_request = SbiRequest::new(
            hart_state.gpr(GpRegister::a7),
            hart_state.gpr(GpRegister::a6),
            hart_state.gpr(GpRegister::a0),
            hart_state.gpr(GpRegister::a1),
            hart_state.gpr(GpRegister::a2),
            hart_state.gpr(GpRegister::a3),
            hart_state.gpr(GpRegister::a4),
            hart_state.gpr(GpRegister::a5),
        );
        Self { sbi_request }
    }

    pub fn sbi_request(&self) -> &SbiRequest {
        &self.sbi_request
    }
}
