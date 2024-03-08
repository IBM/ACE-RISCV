// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use guest_load_page_fault_request::GuestLoadPageFaultRequest;
pub use guest_load_page_fault_result::GuestLoadPageFaultResult;
pub use guest_store_page_fault_request::GuestStorePageFaultRequest;
pub use guest_store_page_fault_result::GuestStorePageFaultResult;
pub use interrupt_request::{EnabledInterrupts, InjectedInterrupts, InterruptRequest};
pub use mmio_load_request::MmioLoadRequest;
pub use mmio_store_request::MmioStoreRequest;
pub use opensbi_request::OpensbiRequest;
pub use opensbi_result::OpensbiResult;
pub use promote_to_confidential_vm_request::PromoteToConfidentialVm;
pub use resume_request::ResumeRequest;
pub use sbi_hsm::{SbiHsmHartStart, SbiHsmHartStatus, SbiHsmHartSuspend};
pub use sbi_ipi::SbiIpi;
pub use sbi_request::SbiRequest;
pub use sbi_result::SbiResult;
pub use sbi_rfence::{SbiRemoteFenceI, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid};
pub use sbi_srst::SbiSrstSystemReset;
pub use sbi_vm_request::SbiVmRequest;
pub use share_page_request::SharePageRequest;
pub use share_page_result::SharePageResult;
pub use terminate_request::TerminateRequest;
pub use unshare_page_request::UnsharePageRequest;
pub use virtual_instruction::{VirtualInstructionRequest, VirtualInstructionResult};

mod guest_load_page_fault_request;
mod guest_load_page_fault_result;
mod guest_store_page_fault_request;
mod guest_store_page_fault_result;
mod interrupt_request;
mod mmio_load_request;
mod mmio_store_request;
mod opensbi_request;
mod opensbi_result;
mod promote_to_confidential_vm_request;
mod resume_request;
mod sbi_hsm;
mod sbi_ipi;
mod sbi_request;
mod sbi_result;
mod sbi_rfence;
mod sbi_srst;
mod sbi_vm_request;
mod share_page_request;
mod share_page_result;
mod terminate_request;
mod unshare_page_request;
mod virtual_instruction;

/// Declassifiers that expose part of the confidential VM's hart state to the hypervisor.
pub enum ExposeToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    OpensbiResult(OpensbiResult),
    SbiVmRequest(SbiVmRequest),
    MmioLoadRequest(MmioLoadRequest),
    MmioStoreRequest(MmioStoreRequest),
    InterruptRequest(InterruptRequest),
    EnabledInterrupts(EnabledInterrupts),
}

/// Declassifiers that expose part of the hypervisor's state to a confidential VM's hart.
pub enum ExposeToConfidentialVm {
    SbiResult(SbiResult),
    GuestLoadPageFaultResult(GuestLoadPageFaultResult),
    VirtualInstructionResult(VirtualInstructionResult),
    GuestStorePageFaultResult(GuestStorePageFaultResult),
    Resume(),
    SbiIpi(SbiIpi),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
    SbiHsmHartStart(),
    SbiHsmHartStartPending(),
    SbiSrstSystemReset(),
}

/// An intermediate confidential hart state that requested certain operation from the hypervisor and is waiting for the
/// response.
#[derive(PartialEq)]
pub enum PendingRequest {
    SharePage(SharePageRequest),
    GuestLoadPageFault(GuestLoadPageFaultRequest),
    GuestStorePageFault(GuestStorePageFaultRequest),
    SbiHsmHartStart(),
    SbiHsmHartStartPending(),
    SbiRequest(),
}

/// A request send from one confidential hart to another confidential hart belonging to the same confidential VM.
#[derive(Debug, PartialEq, Clone)]
pub enum InterHartRequest {
    SbiIpi(SbiIpi),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
    SbiSrstSystemReset(SbiSrstSystemReset),
}

impl InterHartRequest {
    pub fn into_expose_to_confidential_vm(self) -> ExposeToConfidentialVm {
        match self {
            Self::SbiIpi(v) => ExposeToConfidentialVm::SbiIpi(v),
            Self::SbiRemoteFenceI(v) => ExposeToConfidentialVm::SbiRemoteFenceI(v),
            Self::SbiRemoteSfenceVma(v) => ExposeToConfidentialVm::SbiRemoteSfenceVma(v),
            Self::SbiRemoteSfenceVmaAsid(v) => ExposeToConfidentialVm::SbiRemoteSfenceVmaAsid(v),
            Self::SbiSrstSystemReset(_) => ExposeToConfidentialVm::SbiSrstSystemReset(),
        }
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        match self {
            Self::SbiIpi(v) => Self::_is_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
            Self::SbiRemoteFenceI(v) => Self::_is_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
            Self::SbiRemoteSfenceVma(v) => Self::_is_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
            Self::SbiRemoteSfenceVmaAsid(v) => Self::_is_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
            Self::SbiSrstSystemReset(v) => v.initiating_confidential_hart_id != hart_id,
        }
    }

    fn _is_hart_selected(hart_id: usize, hart_mask: usize, hart_mask_base: usize) -> bool {
        // according to SBI documentation all harts are selected when the mask_base is of its maximum value
        match hart_mask_base == usize::MAX {
            true => true,
            false => {
                hart_id.checked_sub(hart_mask_base).filter(|id| *id >= usize::BITS as usize).is_some_and(|id| hart_mask & (1 << id) != 0)
            }
        }
    }
}
