// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{MIE_MTIP_MASK, MIE_SSIP_MASK, MIE_STIP, MIE_STIP_MASK, *};
use crate::core::transformations::{
    ExposeToConfidentialVm, ExposeToHypervisor, InterruptRequest, SbiRequest, SbiResult, VirtualInstructionRequest,
    VirtualInstructionResult,
};
use crate::error::Error;

/// Handles interrupts of a confidential hart.
///
/// The control flows:
/// - to the hypervisor when an interrupt comes from a hardware device.
/// - to the confidential hart in case of software interrupts
pub fn handle_interrupt(mut confidential_flow: ConfidentialFlow) -> ! {
    let mip = confidential_flow.confidential_hart().csrs().mip.read();

    if mip & MIE_SSIP_MASK > 0 {
        // One of the reasons why the confidential hart was interrupted with SSIP is that it got an `InterHartRequest` from
        // another confidential hart. If this is the case, we must process all queued requests before resuming confidential
        // hart's execution.
        //
        // This piece of code executes because a confidential hart was interrupted with supervisor software interrupt to
        // process IPIs.
        confidential_flow.process_inter_hart_requests();
        // It might have happened, that this confidential hart has been shutdown when processing an IPI. I.e., there was
        // an IPI from other confidential hart that requested this confidential hart to shutdown. If this happened, we
        // cannot resume this confidential hart anymore. We must exit to the hypervisor and inform it about it.
        if confidential_flow.is_confidential_hart_shutdown() {
            crate::confidential_flow::handlers::shutdown::shutdown_confidential_hart(confidential_flow);
        }
    }

    // the only interrupts that we can see here are:
    // * M-mode timer that the security monitor set to preemt execution of a confidential VM
    // * M-mode software or external interrupt
    if mip & (MIE_MTIP_MASK | MIE_STIP_MASK) > 0 {
        // inject timer interrupt to the hypervisor
        let transformation = ExposeToHypervisor::InterruptRequest(InterruptRequest::new(MIE_STIP));
        confidential_flow.into_non_confidential_flow().exit_to_hypervisor(transformation)
    } else {
        // resume the hypervisor, it will trap again in the security monitor to process these interrupts
        let transformation = ExposeToHypervisor::SbiResult(SbiResult::success(0));
        confidential_flow.into_non_confidential_flow().exit_to_hypervisor(transformation)
    }
}

/// Handles a hypercall from a confidential hart to hypervisor.
pub fn probe_sbi_extensions(confidential_flow: ConfidentialFlow) -> ! {
    let sbi_request = SbiRequest::from_confidential_hart(confidential_flow.confidential_hart());

    let extension_id = sbi_request.a0();
    let response = match extension_id {
        AceExtension::EXTID => 1,
        BaseExtension::EXTID => 1,
        IpiExtension::EXTID => 1,
        RfenceExtension::EXTID => 1,
        HsmExtension::EXTID => 1,
        SrstExtension::EXTID => 1,
        _ => 0,
    };
    let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::success(response));
    confidential_flow.exit_to_confidential_hart(transformation)
}

/// Handles the situation in which a confidential hart trapped into the security monitor but the security monitor does
/// not support such exception. For example, a confidential hart could trap after making a not supported SBI call.
pub fn invalid_call(confidential_flow: ConfidentialFlow) -> ! {
    let mcause = confidential_flow.confidential_hart().csrs().mcause.read();
    let transformation = Error::InvalidCall(mcause).into_confidential_transformation();
    confidential_flow.exit_to_confidential_hart(transformation)
}

pub fn emulate_instruction(confidential_flow: ConfidentialFlow) -> ! {
    let request = VirtualInstructionRequest::from_confidential_hart(confidential_flow.confidential_hart());
    let transformation = if request.instruction() == WFI_INSTRUCTION {
        ExposeToConfidentialVm::VirtualInstructionResult(VirtualInstructionResult::new(request.instruction_length()))
    } else {
        // TODO: add support for some CSR manipulation
        // TODO: for not supported instructions, inject illegal instruction exception to the guest
        panic!("Not supported virtual instruction: {:x}", request.instruction());
    };
    confidential_flow.exit_to_confidential_hart(transformation)
}
