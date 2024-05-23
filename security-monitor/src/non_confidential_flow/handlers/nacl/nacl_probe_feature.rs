// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::non_confidential_flow::handlers::sbi::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Returns information on supported nested acceleration (NACL) features that security monitor implements.
pub struct NaclProbeFeature {
    feature_id: usize,
}

impl NaclProbeFeature {
    const FEATURE_NOT_AVAILABLE: usize = 0;
    const _FEATURE_AVAILABLE: usize = 1;

    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { feature_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        let is_feature_supported = match self.feature_id {
            _ => Self::FEATURE_NOT_AVAILABLE,
        };
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(SbiResponse::success(is_feature_supported)))
    }
}
