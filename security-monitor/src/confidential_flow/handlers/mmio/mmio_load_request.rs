// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::{MmioAccessFault, MmioLoadPending};
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::is_bit_enabled;
use crate::core::architecture::specification::CAUSE_LOAD_ACCESS;
use crate::core::control_data::{ConfidentialHart, HypervisorHart, ResumableOperation};
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles MMIO load request coming from the confidential hart. This request will be declassified to the hypervisor.
pub struct MmioLoadRequest {
    mcause: usize,
    mtval: usize,
    mtval2: usize,
    mtinst: usize,
    instruction_alignment: Option<usize>,
}

impl MmioLoadRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let mut instruction_alignment = None;
        let mut mtinst = confidential_hart.csrs().mtinst.read();
        if mtinst == 0 {
            let mepc = confidential_hart.csrs().mepc.read_from_main_memory();
            confidential_hart.csrs().mstatus.read_and_set_bits((1 << 17));
            confidential_hart.csrs().mstatus.read_and_set_bits((1 << 19));
            debug!("Load mepc={:x} mastatus={:x}", mepc, confidential_hart.csrs().mstatus.read());
            // enable MPRV and MXR
            // Safety: Below memory reads using raw pointer are safe because:
            //  * RISC-V requires that instructions are properly aligned
            //  * It is the processor who writes mepc with the address of the trapped instruction
            //  * Processor will perform memory address translation using guest's MMU configuration because of mstatus::MPRV
            if mepc % 8 == 0 {
                mtinst = unsafe { (mepc as *const u64).read_volatile() } as usize;
                instruction_alignment = Some(8);
                debug!("Load 8B alignment");
            } else if mepc % 4 == 0 {
                mtinst = unsafe { (mepc as *const u32).read_volatile() } as usize;
                instruction_alignment = Some(4);
                debug!("Load 4B alignment");
            } else if mepc % 2 == 0 {
                mtinst = unsafe { (mepc as *const u16).read_volatile() } as usize;
                instruction_alignment = Some(2);
                debug!("Load 2B alignment");
            } else {
                debug!("Load invalid alignment");
            }
            confidential_hart.csrs().mstatus.read_and_clear_bits((1 << 17));
            confidential_hart.csrs().mstatus.read_and_clear_bits((1 << 19));
            debug!("Load mtinst={:x} mastatus={:x}", mtinst, confidential_hart.csrs().mstatus.read());
        }

        Self {
            mcause: confidential_hart.csrs().mcause.read(),
            mtval: confidential_hart.csrs().mtval.read(),
            mtval2: confidential_hart.csrs().mtval2.read(),
            mtinst,
            instruction_alignment,
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        // According to the RISC-V privilege spec, mtinst encodes faulted instruction (bit 0 is 1) or a pseudo instruction
        if self.mtinst & 0x1 == 0 {
            debug!("Detected pseudo instruction, should never happen!");
        }

        let mut instruction = self.mtinst | 0x3;
        let instruction_length = if is_bit_enabled(self.mtinst, 1) { riscv_decode::instruction_length(instruction as u16) } else { 2 };
        debug!("Load instr len: {} instruction_alignment = {:?}", instruction_length, self.instruction_alignment);

        // Make sure that we do not expose via mtinst more than the trapped instruction. This could happen when security monitor reads
        // the trapped instruction direcly from the guest's main memory but the instruction size is smaller than its alignment.
        // For example, consider that security monitor reads instruction of size 2B that is aligned to 8B. It would read the entire 8B
        // containing 2B instruction + 6B of the next instruction. It must expose only 2B. So, it must determine the size instruction
        // and then mask only bits belonging to this instruction. Otherwise, we would create a cover channel.
        if let Some(alignment) = self.instruction_alignment {
            if alignment < instruction_length {
                debug!("Not aligned instruction read from mepc for mmio load: {} {:x}", instruction_length, instruction);
            } else if alignment > instruction_length {
                instruction = instruction & ((1 << 8 * instruction_length) - 1);
            }
        }

        let fault_address = (self.mtval2 << 2) | (self.mtval & 0x3);
        debug!("Load fault address {:x}", fault_address);
        if !MmioAccessFault::tried_to_access_valid_mmio_region(confidential_flow.confidential_vm_id(), fault_address) {
            let mmio_access_fault_handler = MmioAccessFault::new(CAUSE_LOAD_ACCESS.into(), self.mtval, instruction_length);
            confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::MmioAccessFault(mmio_access_fault_handler));
        }

        match crate::core::architecture::decode_result_register(instruction) {
            Ok(gpr) => confidential_flow
                .set_resumable_operation(ResumableOperation::MmioLoad(MmioLoadPending::new(instruction_length, gpr)))
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
        hypervisor_hart.csrs_mut().scause.write(self.mcause);
        hypervisor_hart.csrs_mut().stval.write(self.mtval);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTVAL.into(), self.mtval2);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTINST.into(), self.mtinst);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
