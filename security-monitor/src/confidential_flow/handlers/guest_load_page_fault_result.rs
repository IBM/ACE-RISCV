// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, GuestLoadPageFaultResult};

pub fn handle(load_fault_result: GuestLoadPageFaultResult, confidential_flow: ConfidentialFlow) -> ! {
    confidential_flow.exit_to_confidential_vm(ExposeToConfidentialVm::GuestLoadPageFaultResult(load_fault_result))
}
