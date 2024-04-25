// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::{GeneralPurposeRegister, CAUSE_VIRTUAL_SUPERVISOR_ECALL};
use crate::core::control_data::{ConfidentialHart, HypervisorHart, PendingRequest};

/// Handles a hypercall from a confidential hart to hypervisor.
pub struct SbiRequest {
    extension_id: usize,
    function_id: usize,
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
}

impl SbiRequest {
    const KVM_ACE_EXTID: usize = 0x509999;
    const KVM_ACE_PAGE_IN_FID: usize = 2;

    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self::new(
            confidential_hart.gprs().read(GeneralPurposeRegister::a7),
            confidential_hart.gprs().read(GeneralPurposeRegister::a6),
            confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            confidential_hart.gprs().read(GeneralPurposeRegister::a1),
            confidential_hart.gprs().read(GeneralPurposeRegister::a2),
            confidential_hart.gprs().read(GeneralPurposeRegister::a3),
            confidential_hart.gprs().read(GeneralPurposeRegister::a4),
            confidential_hart.gprs().read(GeneralPurposeRegister::a5),
        )
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow
            .set_pending_request(PendingRequest::SbiRequest())
            .into_non_confidential_flow()
            .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(self))
    }

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(CAUSE_VIRTUAL_SUPERVISOR_ECALL.into());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a7, self.extension_id);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a6, self.function_id);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a2, self.a2);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a3, self.a3);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a4, self.a4);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a5, self.a5);
        hypervisor_hart.apply_trap(false);
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(CAUSE_VIRTUAL_SUPERVISOR_ECALL.into());
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a7, self.extension_id);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a6, self.function_id);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a1, self.a1);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a2, self.a2);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a3, self.a3);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a4, self.a4);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a5, self.a5);
        hypervisor_hart.apply_trap(false);
    }

    pub fn new(extension_id: usize, function_id: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize) -> Self {
        Self { extension_id, function_id, a0, a1, a2, a3, a4, a5 }
    }

    pub fn kvm_ace_page_in(page_address: usize) -> Self {
        Self::new(Self::KVM_ACE_EXTID, Self::KVM_ACE_PAGE_IN_FID, page_address, 0, 0, 0, 0, 0)
    }

    pub fn kvm_hsm_hart_start(virtual_hart_id: usize) -> Self {
        use crate::core::architecture::HsmExtension;
        Self::new(HsmExtension::EXTID, HsmExtension::HART_START_FID, virtual_hart_id, 0, 0, 0, 0, 0)
    }

    pub fn kvm_hsm_hart_stop() -> Self {
        use crate::core::architecture::HsmExtension;
        Self::new(HsmExtension::EXTID, HsmExtension::HART_STOP_FID, 0, 0, 0, 0, 0, 0)
    }

    pub fn kvm_hsm_hart_suspend() -> Self {
        use crate::core::architecture::HsmExtension;
        Self::new(HsmExtension::EXTID, HsmExtension::HART_SUSPEND_FID, 0, 0, 0, 0, 0, 0)
    }
}
