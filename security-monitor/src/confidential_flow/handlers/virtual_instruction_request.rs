// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, VirtualInstructionRequest, VirtualInstructionResult};

const WFI_INSTRUCTION: usize = 0x10500073;

pub fn handle(request: VirtualInstructionRequest, confidential_flow: ConfidentialFlow) -> ! {
    let transformation = if request.instruction() == WFI_INSTRUCTION {
        ExposeToConfidentialVm::VirtualInstructionResult(VirtualInstructionResult::new(request.instruction_length()))
    } else {
        // TODO: add support for some CSR manipulation
        // TODO: for not supported instructions, inject illegal instruction exception to the guest
        panic!("Not supported virtual instruction: {:x}", request.instruction());
    };
    confidential_flow.exit_to_confidential_hart(transformation)
}
