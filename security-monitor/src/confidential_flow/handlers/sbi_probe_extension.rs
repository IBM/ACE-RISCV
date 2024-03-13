// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::*;
use crate::core::transformations::{ExposeToConfidentialVm, SbiRequest, SbiResult};

/// Handles a hypercall from a confidential hart to hypervisor.
pub fn handle(sbi_request: SbiRequest, confidential_flow: ConfidentialFlow) -> ! {
    let extension_id = sbi_request.a0();
    let response = match extension_id {
        AceExtension::EXTID => 1,
        BaseExtension::EXTID => 1,
        IpiExtension::EXTID => 1,
        RfenceExtension::EXTID => 1,
        HsmExtension::EXTID => 1,
        SrstExtension::EXTID => 1,
        _ => 0,
    };
    let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::success(response));
    confidential_flow.exit_to_confidential_hart(transformation)
}
