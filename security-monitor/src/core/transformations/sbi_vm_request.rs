// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::control_data::HypervisorHart;
use crate::core::transformations::SbiRequest;

pub struct SbiVmRequest {
    sbi_request: SbiRequest,
}

impl SbiVmRequest {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            sbi_request: SbiRequest::new(
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a7),
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a6),
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a0),
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a2),
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a3),
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a4),
                hypervisor_hart.gprs().read(GeneralPurposeRegister::a5),
            ),
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        use crate::core::architecture::CAUSE_VIRTUAL_SUPERVISOR_ECALL;
        hypervisor_hart.csrs_mut().scause.set(CAUSE_VIRTUAL_SUPERVISOR_ECALL.into());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a7, self.sbi_request.extension_id());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a6, self.sbi_request.function_id());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.sbi_request.a0());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.sbi_request.a1());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a2, self.sbi_request.a2());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a3, self.sbi_request.a3());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a4, self.sbi_request.a4());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a5, self.sbi_request.a5());
        hypervisor_hart.apply_trap(false);
    }
}
