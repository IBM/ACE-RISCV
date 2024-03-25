// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{is_bit_enabled, GeneralPurposeRegister};
use crate::core::control_data::{ConfidentialHart, HardwareHart, HypervisorHart};
use crate::error::Error;

pub struct MmioLoadRequest {
    code: usize,
    stval: usize,
    htval: usize,
    instruction: usize,
    instruction_length: usize,
    gpr: GeneralPurposeRegister,
}

impl MmioLoadRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Result<Self, Error> {
        let mcause = confidential_hart.confidential_hart_state().csrs().mcause.read();
        let mtinst = confidential_hart.confidential_hart_state().csrs().mtinst.read();
        let mtval = confidential_hart.confidential_hart_state().csrs().mtval.read();
        let mtval2 = confidential_hart.confidential_hart_state().csrs().mtval2.read();
        // According to the RISC-V privilege spec, mtinst encodes faulted instruction (bit 0 is 1) or a pseudo instruction
        assert!(mtinst & 0x1 > 0);
        let instruction = mtinst | 0x3;
        let instruction_length = if is_bit_enabled(mtinst, 1) { riscv_decode::instruction_length(instruction as u16) } else { 2 };
        let gpr = crate::core::architecture::decode_result_register(instruction)?;

        Ok(Self { code: mcause, stval: mtval, htval: mtval2, instruction: mtinst, instruction_length, gpr })
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(self.code);
        // KVM uses htval and stval to recreate the fault address
        hypervisor_hart.csrs_mut().stval.set(self.stval);
        hypervisor_hart.csrs_mut().htval.set(self.htval);
        // Hack: we do not allow the hypervisor to look into the guest memory but we have to inform him about the instruction that caused
        // exception. our approach is to expose this instruction via vsscratch. In future, we should move to RISC-V NACL extensions.
        hypervisor_hart.csrs_mut().vsscratch.set(self.instruction);
        hypervisor_hart.apply_trap(true);
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }

    pub fn gpr(&self) -> GeneralPurposeRegister {
        self.gpr
    }
}

pub struct MmioStoreRequest {
    code: usize,
    stval: usize,
    htval: usize,
    instruction: usize,
    instruction_length: usize,
    gpr: GeneralPurposeRegister,
    gpr_value: usize,
}

impl MmioStoreRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Result<Self, Error> {
        let mcause = confidential_hart.confidential_hart_state().csrs().mcause.read();
        let mtinst = confidential_hart.confidential_hart_state().csrs().mtinst.read();
        let mtval = confidential_hart.confidential_hart_state().csrs().mtval.read();
        let mtval2 = confidential_hart.confidential_hart_state().csrs().mtval2.read();

        // According to the RISC-V privilege spec, mtinst encodes faulted instruction (bit 0 is 1) or a pseudo instruction
        assert!(mtinst & 0x1 > 0);
        let instruction = mtinst | 0x3;
        let instruction_length = if is_bit_enabled(mtinst, 1) { riscv_decode::instruction_length(instruction as u16) } else { 2 };
        let gpr = crate::core::architecture::decode_result_register(instruction)?;
        let gpr_value = confidential_hart.confidential_hart_state().gprs().read(gpr);

        Ok(Self { code: mcause, stval: mtval, htval: mtval2, instruction: mtinst, instruction_length, gpr, gpr_value })
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(self.code);
        // KVM uses htval and stval to recreate the fault address
        hypervisor_hart.csrs_mut().stval.set(self.stval);
        hypervisor_hart.csrs_mut().htval.set(self.htval);
        hypervisor_hart.gprs_mut().write(self.gpr, self.gpr_value);
        // Hack: we do not allow the hypervisor to look into the guest memory but we have to inform him about the instruction that caused
        // exception. our approach is to expose this instruction via vsscratch. In future, we should move to RISC-V NACL extensions.
        hypervisor_hart.csrs_mut().vsscratch.set(self.instruction);
        hypervisor_hart.apply_trap(true);
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}
