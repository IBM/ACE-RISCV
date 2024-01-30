// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, GuestStorePageFaultRequest, GuestStorePageFaultResult};

pub fn handle(confidential_flow: ConfidentialFlow, request: GuestStorePageFaultRequest) -> ! {
    let transformation = ExposeToConfidentialVm::GuestStorePageFaultResult(GuestStorePageFaultResult::new(request));
    confidential_flow.exit_to_confidential_hart(transformation)
}
