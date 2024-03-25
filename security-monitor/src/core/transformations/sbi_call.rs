// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState, ECALL_INSTRUCTION_LENGTH};
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, HypervisorHart};

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
    const KVM_ACE_REGISTER_FID: usize = 1;
    const KVM_ACE_PAGE_IN_FID: usize = 2;

    pub fn kvm_ace_register(confidential_vm_id: ConfidentialVmId, confidential_hart_id: usize) -> Self {
        Self::new(Self::KVM_ACE_EXTID, Self::KVM_ACE_REGISTER_FID, confidential_vm_id.usize(), confidential_hart_id, 0, 0, 0, 0)
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

    pub fn kvm_srst_system_reset() -> Self {
        use crate::core::architecture::SrstExtension;
        Self::new(SrstExtension::EXTID, SrstExtension::SYSTEM_RESET_FID, 0, 0, 0, 0, 0, 0)
    }

    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self::new(
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a7),
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a6),
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a0),
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a1),
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a2),
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a3),
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a4),
            confidential_hart.confidential_hart_state().gprs().read(GeneralPurposeRegister::a5),
        )
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        use crate::core::architecture::CAUSE_VIRTUAL_SUPERVISOR_ECALL;
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

    pub fn new(extension_id: usize, function_id: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize) -> Self {
        Self { extension_id, function_id, a0, a1, a2, a3, a4, a5 }
    }

    pub fn extension_id(&self) -> usize {
        self.extension_id
    }

    pub fn function_id(&self) -> usize {
        self.function_id
    }

    pub fn a0(&self) -> usize {
        self.a0
    }

    pub fn a1(&self) -> usize {
        self.a1
    }

    pub fn a2(&self) -> usize {
        self.a2
    }

    pub fn a3(&self) -> usize {
        self.a3
    }

    pub fn a4(&self) -> usize {
        self.a4
    }

    pub fn a5(&self) -> usize {
        self.a5
    }
}

/// Sbi is a result of the SBI call from the Hypervisor to the SBI
/// firmware or a result of the SBI call to the security monitor.
#[derive(Debug)]
pub struct SbiResult {
    a0: usize,
    a1: usize,
    pc_offset: usize,
}

impl SbiResult {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self::new(
            hypervisor_hart.gprs().read(GeneralPurposeRegister::a0),
            hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
            ECALL_INSTRUCTION_LENGTH,
        )
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.confidential_hart_state_mut().gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        confidential_hart.confidential_hart_state_mut().gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
        let new_mepc = confidential_hart.confidential_hart_state().csrs().mepc.read_value() + self.pc_offset;
        confidential_hart.confidential_hart_state_mut().csrs_mut().mepc.save_value(new_mepc);
    }

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        let new_mepc = hypervisor_hart.csrs().mepc.read_value() + self.pc_offset;
        hypervisor_hart.csrs_mut().mepc.save_value(new_mepc);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
    }

    pub fn success(code: usize) -> Self {
        Self::new(0, code, ECALL_INSTRUCTION_LENGTH)
    }

    pub fn failure(code: usize) -> Self {
        Self::new(code, 0, ECALL_INSTRUCTION_LENGTH)
    }

    fn new(a0: usize, a1: usize, pc_offset: usize) -> Self {
        Self { a0, a1, pc_offset }
    }
}
