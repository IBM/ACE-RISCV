// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::core::architecture::riscv::specification::CAUSE_VIRTUAL_SUPERVISOR_ECALL;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;

pub struct SbiRequest {
    extension_id: usize,
    function_id: usize,
    a0: usize,
    a1: usize,
}

impl SbiRequest {
    pub fn new(extension_id: usize, function_id: usize, a0: usize, a1: usize) -> Self {
        Self { extension_id, function_id, a0, a1 }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.write(CAUSE_VIRTUAL_SUPERVISOR_ECALL.into());
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a7, self.extension_id);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a6, self.function_id);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a1, self.a1);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a2, 0);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a3, 0);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a4, 0);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a5, 0);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
