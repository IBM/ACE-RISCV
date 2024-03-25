// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{ExposeToHypervisor, SbiVmRequest};
use crate::non_confidential_flow::NonConfidentialFlow;

pub fn handle(non_confidential_flow: NonConfidentialFlow) -> ! {
    let request = SbiVmRequest::from_hypervisor_hart(non_confidential_flow.hypervisor_hart());
    non_confidential_flow.exit_to_hypervisor(ExposeToHypervisor::SbiVmRequest(request))
}
