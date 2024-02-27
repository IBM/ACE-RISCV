// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{CSR, MIE_SSIP_MASK};
use crate::core::transformations::ExposeToHypervisor;

/// Handles interrupts of a confidential hart.
///
/// The control flows:
/// - to the hypervisor when an interrupt comes from a hardware device.
/// - to the confidential hart in case of software interrupts
pub fn handle(mut confidential_flow: ConfidentialFlow) -> ! {
    let mip = CSR.mip.read();
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
            crate::confidential_flow::handlers::shutdown_confidential_hart::handle(confidential_flow);
        }
    }

    let transformation = ExposeToHypervisor::InterruptRequest();
    confidential_flow.into_non_confidential_flow().exit_to_hypervisor(transformation)
}
