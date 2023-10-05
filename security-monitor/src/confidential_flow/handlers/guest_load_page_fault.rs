// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToHypervisor, GuestLoadPageFaultRequest, MmioLoadRequest, PendingRequest};
use crate::error::Error;

pub fn handle(
    load_fault_request: Result<(GuestLoadPageFaultRequest, MmioLoadRequest), Error>,
    confidential_flow: ConfidentialFlow,
) -> ! {
    match load_fault_request {
        Ok((request, mmio)) => confidential_flow
            .set_pending_request(PendingRequest::GuestLoadPageFault(request))
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::MmioLoadRequest(mmio)),
        Err(error) => confidential_flow
            .into_non_confidential_flow()
            .exit_to_hypervisor(error.into_non_confidential_transformation()),
    }
}
