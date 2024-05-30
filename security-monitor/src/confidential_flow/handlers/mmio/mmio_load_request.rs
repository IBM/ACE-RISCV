// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::MmioLoadPending;
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::is_bit_enabled;
use crate::core::control_data::{ConfidentialHart, HypervisorHart, PendingRequest};
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles MMIO load request coming from the confidential hart. This request will be declassified to the hypervisor.
pub struct MmioLoadRequest {
    mcause: usize,
    mtval: usize,
    mtval2: usize,
    mtinst: usize,
}

impl MmioLoadRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            mcause: confidential_hart.csrs().mcause.read(),
            mtval: confidential_hart.csrs().mtval.read(),
            mtval2: confidential_hart.csrs().mtval2.read(),
            mtinst: confidential_hart.csrs().mtinst.read(),
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        // According to the RISC-V privilege spec, mtinst encodes faulted instruction (bit 0 is 1) or a pseudo instruction
        assert!(self.mtinst & 0x1 > 0);
        let instruction = self.mtinst | 0x3;
        let instruction_length = if is_bit_enabled(self.mtinst, 1) { riscv_decode::instruction_length(instruction as u16) } else { 2 };

        match crate::core::architecture::decode_result_register(instruction) {
            Ok(gpr) => confidential_flow
                .set_pending_request(PendingRequest::MmioLoad(MmioLoadPending::new(instruction_length, gpr)))
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::MmioLoadRequest(self)),
            Err(error) => {
                let transformation = DeclassifyToHypervisor::SbiResponse(SbiResponse::error(error));
                confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(transformation)
            }
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        use crate::core::architecture::riscv::specification::*;
        // The security monitor exposes `scause` and `stval` via hart's CSRs but `htval` and `htinst` via the NACL shared memory.
        hypervisor_hart.csrs_mut().scause.set(self.mcause);
        hypervisor_hart.csrs_mut().stval.set(self.mtval);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTVAL.into(), self.mtval2);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTINST.into(), self.mtinst);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
