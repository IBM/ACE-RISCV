// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::sbi::HsmExtension;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Suspends a confidential hart that made this request. This is an implementation of the HartSuspend function from the
/// HSM extension of SBI.
///
/// The request to suspend the confidential hart comes from the confidential hart itself. The security monitor suspends
/// the confidential hart and informs about it the hypervisor. This functions returns an error to the calling
/// confidential hart if this confidential hart cannot be suspended, for example, because it is not in the started
/// state.
pub struct SbiHsmHartSuspend {
    _suspend_type: usize,
    _resume_address: usize,
    _opaque: usize,
}

impl SbiHsmHartSuspend {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let _suspend_type = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let _resume_address = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        let _opaque = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        Self { _suspend_type, _resume_address, _opaque }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let sbi_request = self.kvm_hsm_hart_suspend();
        match confidential_flow.suspend_confidential_hart(self) {
            Ok(_) => confidential_flow
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(sbi_request)),
            Err(error) => {
                confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::error(error)))
            }
        }
    }

    pub fn kvm_hsm_hart_suspend(&self) -> SbiRequest {
        SbiRequest::new(HsmExtension::EXTID, HsmExtension::HART_SUSPEND_FID, 0, 0)
    }
}
