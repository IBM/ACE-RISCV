// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::{ControlData, HardwareHart};
use crate::core::transformations::{ExposeToHypervisor, ResumeRequest};
use crate::error::Error;

extern "C" {
    fn exit_to_hypervisor_asm() -> !;
}

/// This control flow structure acts like a wrapper around HardwareHart. HardwareHart is never exposed
pub struct NonConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> NonConfidentialFlow<'a> {
    /// This token can be created only by the code owning a mutable reference to
    /// the HardwareHart. This can be only the router and the ConfidentialFlow.
    pub fn create(hardware_hart: &'a mut HardwareHart) -> Self {
        Self { hardware_hart }
    }

    pub fn into_confidential_flow(
        self, resume_request: ResumeRequest,
    ) -> Result<ConfidentialFlow<'a>, (NonConfidentialFlow<'a>, Error)> {
        let confidential_vm_id = resume_request.confidential_vm_id();
        let confidential_hart_id = resume_request.confidential_hart_id();
        match ControlData::try_confidential_vm(confidential_vm_id, |mut cvm| {
            cvm.steal_confidential_hart(confidential_hart_id, self.hardware_hart)
        }) {
            Ok(_) => {
                crate::core::pmp::open_access_to_confidential_memory();
                Ok(ConfidentialFlow::create(self.hardware_hart))
            }
            Err(error) => Err((self, error)),
        }
    }

    pub fn route(self) -> ! {
        use crate::core::transformations::TrapReason;
        use crate::non_confidential_flow::handlers::{esm, invalid_call, opensbi, resume, terminate, vm_hypercall};
        use crate::ACE_EXT_ID;
        const ESM_FID: usize = 1000;
        const RESUME_FID: usize = 1010;
        const TERMINATE_FID: usize = 3001;

        match self.hardware_hart.trap_reason() {
            TrapReason::Interrupt => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            TrapReason::VsEcall(ACE_EXT_ID, ESM_FID) => esm::handle(self.hardware_hart.esm_request(), self),
            TrapReason::VsEcall(ACE_EXT_ID, function_id) => invalid_call::handle(self, ACE_EXT_ID, function_id),
            TrapReason::VsEcall(_, _) => vm_hypercall::handle(self.hardware_hart.sbi_vm_request(), self),
            TrapReason::HsEcall(ACE_EXT_ID, RESUME_FID) => resume::handle(self.hardware_hart.resume_request(), self),
            TrapReason::HsEcall(ACE_EXT_ID, TERMINATE_FID) => {
                terminate::handle(self.hardware_hart.terminate_request(), self)
            }
            TrapReason::HsEcall(ACE_EXT_ID, function_id) => invalid_call::handle(self, ACE_EXT_ID, function_id),
            TrapReason::HsEcall(_, _) => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            TrapReason::StoreAccessFault => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            TrapReason::GuestLoadPageFault => {
                panic!("Bug: Incorrect interrupt delegation configuration")
            }
            TrapReason::GuestStorePageFault => {
                panic!("Bug: Incorrect interrupt delegation configuration")
            }
            TrapReason::Unknown(extension_id, function_id) => invalid_call::handle(self, extension_id, function_id),
        }
    }

    pub fn exit_to_hypervisor(self, transformation: ExposeToHypervisor) -> ! {
        self.hardware_hart.apply(&transformation);
        unsafe { exit_to_hypervisor_asm() }
    }

    pub fn swap_mscratch(&mut self) {
        self.hardware_hart.swap_mscratch()
    }
}
