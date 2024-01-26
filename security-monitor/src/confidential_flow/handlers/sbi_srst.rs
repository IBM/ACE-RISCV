// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::transformations::{ExposeToHypervisor, SbiRequest};

pub fn handle(request: SbiRequest, confidential_flow: ConfidentialFlow) -> ! {
    let confidential_vm_id = confidential_flow.confidential_vm_id();
    match ControlData::try_write(|control_data| control_data.remove_confidential_vm(confidential_vm_id)) {
        Ok(_) => {
            confidential_flow.into_non_confidential_flow().exit_to_hypervisor(ExposeToHypervisor::SbiRequest(request))
        }
        Err(error) => confidential_flow.exit_to_confidential_vm(error.into_confidential_transformation()),
    }
}
