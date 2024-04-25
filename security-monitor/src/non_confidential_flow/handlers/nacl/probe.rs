// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::core::architecture::{GeneralPurposeRegister, NaclExtension};
use crate::core::control_data::HypervisorHart;
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct ProbeNacl {
    _feature_id: usize,
}

impl ProbeNacl {
    const FEATURE_NOT_AVAILABLE: usize = 0;
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { _feature_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        non_confidential_flow
            .apply_and_exit_to_hypervisor(ApplyToHypervisor::SbiResponse(SbiResponse::success(Self::FEATURE_NOT_AVAILABLE)))
    }
}
