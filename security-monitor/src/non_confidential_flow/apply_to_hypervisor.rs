// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::non_confidential_flow::handlers::cove_host_extension::PromoteToConfidentialVm;
use crate::non_confidential_flow::handlers::nested_acceleration_extension::NaclSetupSharedMemory;
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;

/// Transformation of the hypervisor state created as a result of processing an SBI request from the hypervisor.
pub enum ApplyToHypervisorHart {
    SbiResponse(SbiResponse),
    SetSharedMemory(NaclSetupSharedMemory),
    PromoteResponse((PromoteToConfidentialVm, SbiResponse)),
}
