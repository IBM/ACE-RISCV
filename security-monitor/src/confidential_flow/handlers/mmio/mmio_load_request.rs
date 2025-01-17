// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::{MmioAccessFault, MmioLoadPending};
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::specification::{CAUSE_LOAD_ACCESS, *};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, HypervisorHart, ResumableOperation};
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles MMIO load request coming from the confidential hart. This request will be declassified to the hypervisor.
pub struct MmioLoadRequest {
    mcause: usize,
    mtval: usize,
    mtval2: usize,
    instruction: usize,
    instruction_length: usize,
}

impl MmioLoadRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let fault_address = (confidential_hart.csrs().mtval2.read() << 2) | (confidential_hart.csrs().mtval.read() & 0x3);
        debug!("MMIO store: 0x{:x}", fault_address);

        let (instruction, instruction_length) = super::read_trapped_instruction(confidential_hart);
        Self {
            mcause: confidential_hart.csrs().mcause.read(),
            mtval: confidential_hart.csrs().mtval.read(),
            mtval2: confidential_hart.csrs().mtval2.read(),
            instruction,
            instruction_length,
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let fault_address = (self.mtval2 << 2) | (self.mtval & 0x3);
        // if !MmioAccessFault::tried_to_access_valid_mmio_region(confidential_flow.confidential_vm_id(), fault_address) {
        //     let mmio_access_fault_handler = MmioAccessFault::new(CAUSE_LOAD_ACCESS.into(), self.mtval, self.instruction_length);
        //     confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::MmioAccessFault(mmio_access_fault_handler));
        // }

        match crate::core::architecture::decode_result_register(self.instruction) {
            Ok(gpr) => confidential_flow
                .set_resumable_operation(ResumableOperation::MmioLoad(MmioLoadPending::new(self.instruction_length, gpr)))
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::MmioLoadRequest(self)),
            Err(error) => {
                let transformation = DeclassifyToHypervisor::SbiResponse(SbiResponse::error(error));
                confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(transformation)
            }
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        let mut mtinst = if self.instruction & INSN_MASK_LB == INSN_MATCH_LB {
            INSN_MATCH_LB
        } else if self.instruction & INSN_MASK_LBU == INSN_MATCH_LBU {
            INSN_MATCH_LBU
        } else if self.instruction & INSN_MASK_LH == INSN_MATCH_LH {
            INSN_MATCH_LH
        } else if self.instruction & INSN_MASK_LHU == INSN_MATCH_LHU {
            INSN_MATCH_LHU
        } else if self.instruction & INSN_MASK_LW == INSN_MATCH_LW {
            INSN_MATCH_LW
        } else if self.instruction & INSN_MASK_C_LW == INSN_MATCH_C_LW {
            INSN_MATCH_LW
        } else if self.instruction & INSN_MASK_LWU == INSN_MATCH_LWU {
            INSN_MATCH_LWU
        } else if self.instruction & INSN_MASK_LD == INSN_MATCH_LD {
            INSN_MATCH_LD
        } else if self.instruction & INSN_MASK_C_LD == INSN_MATCH_C_LD {
            INSN_MATCH_LD
        } else {
            debug!("Not supported load instruction {:x}", self.instruction);
            0
        };

        mtinst = mtinst | ((GeneralPurposeRegister::a0 as usize) << 7) | 1 << 0;
        if self.instruction_length != 2 {
            mtinst = mtinst | 1 << 1;
        }

        // The security monitor exposes `scause` and `stval` via hart's CSRs but `htval` and `htinst` via the NACL shared memory.
        hypervisor_hart.csrs_mut().scause.write(self.mcause);
        hypervisor_hart.csrs_mut().stval.write(self.mtval);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTVAL.into(), self.mtval2);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTINST.into(), mtinst);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
