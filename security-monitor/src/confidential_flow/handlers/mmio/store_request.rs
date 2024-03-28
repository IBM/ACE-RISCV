// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::MmioStorePending;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::{is_bit_enabled, GeneralPurposeRegister};
use crate::core::control_data::{ConfidentialHart, HypervisorHart, PendingRequest};
use crate::error::Error;

pub struct MmioStoreRequest {
    mcause: usize,
    mtval: usize,
    mtval2: usize,
    mtinst: usize,
    instruction_length: usize,
    gpr: Result<GeneralPurposeRegister, Error>,
    gpr_value: usize,
}

impl MmioStoreRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let mcause = confidential_hart.csrs().mcause.read();
        let mtinst = confidential_hart.csrs().mtinst.read();
        let mtval = confidential_hart.csrs().mtval.read();
        let mtval2 = confidential_hart.csrs().mtval2.read();

        // According to the RISC-V privilege spec, mtinst encodes faulted instruction (bit 0 is 1) or a pseudo instruction
        assert!(mtinst & 0x1 > 0);
        let instruction = mtinst | 0x3;
        let instruction_length = if is_bit_enabled(mtinst, 1) { riscv_decode::instruction_length(instruction as u16) } else { 2 };
        let gpr = crate::core::architecture::decode_result_register(instruction);
        let gpr_value = gpr.as_ref().and_then(|ref gpr| Ok(confidential_hart.gprs().read(**gpr))).unwrap_or(0);

        Self { mcause, mtval, mtval2, mtinst, instruction_length, gpr, gpr_value }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        match self.gpr {
            Ok(_) => confidential_flow
                .set_pending_request(PendingRequest::MmioStore(MmioStorePending::new(self.instruction_length)))
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::MmioStoreRequest(self)),
            Err(error) => {
                confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(error.into_non_confidential_declassifier())
            }
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(self.mcause);
        // KVM uses htval and stval to recreate the fault address
        hypervisor_hart.csrs_mut().stval.set(self.mtval);
        hypervisor_hart.csrs_mut().htval.set(self.mtval2);
        hypervisor_hart.gprs_mut().write(*self.gpr.as_ref().unwrap_or(&GeneralPurposeRegister::zero), self.gpr_value);
        // Hack: we do not allow the hypervisor to look into the guest memory but we have to inform him about the instruction that caused
        // exception. our approach is to expose this instruction via vsscratch. In future, we should move to RISC-V NACL extensions.
        hypervisor_hart.csrs_mut().vsscratch.set(self.mtinst);
        hypervisor_hart.apply_trap(true);
    }
}
