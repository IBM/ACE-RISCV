// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::non_confidential_flow::handlers::nacl::NaclSetupSharedMemory;
use crate::non_confidential_flow::handlers::opensbi::DelegateToOpensbi;

/// Transformation of the hypervisor state created as a result of processing an SBI request from the hypervisor.
pub enum ApplyToHypervisorHart {
    SbiResponse(SbiResponse),
    OpenSbiResponse(DelegateToOpensbi),
    SetSharedMemory(NaclSetupSharedMemory),
}
