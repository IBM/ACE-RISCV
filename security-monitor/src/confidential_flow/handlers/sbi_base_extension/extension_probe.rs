// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::sbi::*;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;

/// Returns information whether the confidential VM has access to the specific SBI extension.
pub struct SbiExtensionProbe {
    extension_id: usize,
}

impl SbiExtensionProbe {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { extension_id: confidential_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = ApplyToConfidentialHart::SbiResponse(SbiResponse::success_with_code(self.supported_sbi_extensions()));
        confidential_flow.apply_and_exit_to_confidential_hart(transformation)
    }

    fn supported_sbi_extensions(&self) -> usize {
        match self.extension_id {
            BaseExtension::EXTID => 1,
            IpiExtension::EXTID => 1,
            RfenceExtension::EXTID => 1,
            HsmExtension::EXTID => 1,
            SrstExtension::EXTID => 1,
            CovgExtension::EXTID => 1,
            TimeExtension::EXTID => 1,
            _ => 0,
        }
    }
}
