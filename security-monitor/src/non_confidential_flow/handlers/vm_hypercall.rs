// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{ExposeToHypervisor, SbiVmRequest};
use crate::non_confidential_flow::NonConfidentialFlow;

pub fn handle(sbi_request_from_vm: SbiVmRequest, non_confidential_flow: NonConfidentialFlow) -> ! {
    non_confidential_flow.exit_to_hypervisor(ExposeToHypervisor::SbiVmRequest(sbi_request_from_vm))
}
