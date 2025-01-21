// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::{MmioAccessFault, MmioStorePending};
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::specification::{CAUSE_STORE_ACCESS, *};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, HypervisorHart, ResumableOperation};
use crate::error::Error;
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles MMIO store request coming from the confidential hart. This request will be declassified to the hypervisor.
pub struct MmioStoreRequest {
    mcause: usize,
    mtval: usize,
    mtval2: usize,
    instruction: usize,
    instruction_length: usize,
    gpr_value: Result<usize, Error>,
}

impl MmioStoreRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let mcause = confidential_hart.csrs().mcause.read();
        let mtval = confidential_hart.csrs().mtval.read();
        let mtval2 = confidential_hart.csrs().mtval2.read();

        let fault_address = (mtval2 << 2) | (mtval & 0x3);
        // debug!("MMIO store: 0x{:x}", fault_address);

        let (instruction, instruction_length) = super::read_trapped_instruction(confidential_hart);
        let gpr_value =
            crate::core::architecture::decode_result_register(instruction).and_then(|gpr| Ok(confidential_hart.gprs().read(gpr)));
        Self { mcause, mtval, mtval2, instruction, instruction_length, gpr_value }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let fault_address = (self.mtval2 << 2) | (self.mtval & 0x3);

        // if !MmioAccessFault::tried_to_access_valid_mmio_region(confidential_flow.confidential_vm_id(), fault_address) {
        //     let mmio_access_fault_handler = MmioAccessFault::new(CAUSE_STORE_ACCESS.into(), self.mtval, self.instruction_length);
        //     confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::MmioAccessFault(mmio_access_fault_handler));
        // }

        match self.gpr_value {
            Ok(_) => confidential_flow
                .set_resumable_operation(ResumableOperation::MmioStore(MmioStorePending::new(self.instruction_length)))
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::MmioStoreRequest(self)),
            Err(error) => {
                let transformation = DeclassifyToHypervisor::SbiResponse(SbiResponse::error(error));
                confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(transformation)
            }
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        let mut mtinst = if self.instruction & INSN_MASK_SB == INSN_MATCH_SB {
            INSN_MATCH_SB
        } else if self.instruction & INSN_MASK_SH == INSN_MATCH_SH {
            INSN_MATCH_SH
        } else if self.instruction & INSN_MASK_SW == INSN_MATCH_SW {
            INSN_MATCH_SW
        } else if self.instruction & INSN_MASK_C_SW == INSN_MATCH_C_SW {
            INSN_MATCH_SW
        } else if self.instruction & INSN_MASK_SD == INSN_MATCH_SD {
            INSN_MATCH_SD
        } else if self.instruction & INSN_MASK_C_SD == INSN_MATCH_C_SD {
            INSN_MATCH_SD
        } else {
            debug!("Not supported store instruction {:x}", self.instruction);
            0
        };

        mtinst |= ((GeneralPurposeRegister::a0 as usize) << 20) | 1 << 0;
        if self.instruction_length != 2 {
            mtinst |= 1 << 1;
        }

        hypervisor_hart.csrs_mut().scause.write(self.mcause);
        hypervisor_hart.csrs_mut().stval.write(self.mtval);
        hypervisor_hart.shared_memory_mut().write_gpr(GeneralPurposeRegister::a0, *self.gpr_value.as_ref().unwrap_or(&0));
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTVAL.into(), self.mtval2);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTINST.into(), mtinst);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
