// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResult;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{GeneralPurposeRegister, *};
use crate::core::control_data::ConfidentialHart;
use crate::core::transformations::ExposeToConfidentialVm;

pub struct SbiExtensionProbe {
    extension_id: usize,
}

impl SbiExtensionProbe {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { extension_id: confidential_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    /// Handles the situation in which a confidential hart trapped into the security monitor but the security monitor does
    /// not support such exception. For example, a confidential hart could trap after making a not supported SBI call.
    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let response = match self.extension_id {
            AceExtension::EXTID => 1,
            BaseExtension::EXTID => 1,
            IpiExtension::EXTID => 1,
            RfenceExtension::EXTID => 1,
            HsmExtension::EXTID => 1,
            SrstExtension::EXTID => 1,
            _ => 0,
        };
        let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::success(response));
        confidential_flow.exit_to_confidential_hart(transformation)
    }
}
