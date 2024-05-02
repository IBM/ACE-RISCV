// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::core::architecture::{GeneralPurposeRegister, CAUSE_VIRTUAL_SUPERVISOR_ECALL};
use crate::core::control_data::HypervisorHart;

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
    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        debug!("SBI declassify {:x} {}", self.extension_id, self.function_id);
        hypervisor_hart.csrs_mut().scause.set(CAUSE_VIRTUAL_SUPERVISOR_ECALL.into());
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a7, self.extension_id);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a6, self.function_id);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a1, self.a1);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a2, self.a2);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a3, self.a3);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a4, self.a4);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a5, self.a5);
        SbiResponse::success(0).declassify_to_hypervisor_hart(hypervisor_hart);
    }

    pub fn new(extension_id: usize, function_id: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize) -> Self {
        Self { extension_id, function_id, a0, a1, a2, a3, a4, a5 }
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
