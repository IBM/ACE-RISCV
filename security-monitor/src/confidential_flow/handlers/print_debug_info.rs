// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{GpRegister, HartArchitecturalState};
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult};
use crate::error::Error;

/// Handles the situation in which a confidential hart trapped into the security monitor but the security monitor does
/// not support such exception. For example, a confidential hart could trap after making a not supported SBI call.
pub fn handle(confidential_hart_state: HartArchitecturalState, confidential_flow: ConfidentialFlow) -> ! {
    let a0 = confidential_hart_state.gpr(GpRegister::a0);
    let a1 = confidential_hart_state.gpr(GpRegister::a1);
    let a2 = confidential_hart_state.gpr(GpRegister::a2);

    debug!("CVM debug: a0={} a1={} a2={} [pc={:x}]", a0, a1, a2, confidential_hart_state.mepc);
    let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::success(0));
    confidential_flow.exit_to_confidential_hart(transformation)
}
