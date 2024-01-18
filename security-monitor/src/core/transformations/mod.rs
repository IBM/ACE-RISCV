// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use convert_to_confidential_vm_request::ConvertToConfidentialVm;
pub use guest_load_page_fault_request::GuestLoadPageFaultRequest;
pub use guest_load_page_fault_result::GuestLoadPageFaultResult;
pub use guest_store_page_fault_request::GuestStorePageFaultRequest;
pub use guest_store_page_fault_result::GuestStorePageFaultResult;
pub use interrupt_request::InterruptRequest;
pub use mmio_load_request::MmioLoadRequest;
pub use mmio_store_request::MmioStoreRequest;
pub use opensbi_request::OpensbiRequest;
pub use resume_request::ResumeRequest;
pub use sbi_hsm::SbiHsmHartStart;
pub use sbi_ipi::SbiIpi;
pub use sbi_request::SbiRequest;
pub use sbi_result::SbiResult;
pub use sbi_rfence::{SbiRemoteFenceI, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid};
pub use sbi_vm_request::SbiVmRequest;
pub use share_page_request::{ConfidentialVmVirtualAddress, SharePageRequest};
pub use share_page_result::SharePageResult;
pub use terminate_request::TerminateRequest;

mod convert_to_confidential_vm_request;
mod guest_load_page_fault_request;
mod guest_load_page_fault_result;
mod guest_store_page_fault_request;
mod guest_store_page_fault_result;
mod interrupt_request;
mod mmio_load_request;
mod mmio_store_request;
mod opensbi_request;
mod resume_request;
mod sbi_hsm;
mod sbi_ipi;
mod sbi_request;
mod sbi_result;
mod sbi_rfence;
mod sbi_vm_request;
mod share_page_request;
mod share_page_result;
mod terminate_request;

/// Declassifiers that expose part of the confidential VM's hart state to the hypervisor.
pub enum ExposeToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    SbiVmRequest(SbiVmRequest),
    MmioLoadRequest(MmioLoadRequest),
    MmioStoreRequest(MmioStoreRequest),
    InterruptRequest(InterruptRequest),
}

/// Declassifiers that expose part of the hypervisor's state to a confidential VM's hart.
pub enum ExposeToConfidentialVm {
    SbiResult(SbiResult),
    GuestLoadPageFaultResult(GuestLoadPageFaultResult),
    GuestStorePageFaultResult(GuestStorePageFaultResult),
    Resume(),
    InterProcessorInterrupt(SbiIpi),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
    SbiHsmHartStart(SbiHsmHartStart),
}

/// An intermediate confidential hart state that requested certain operation from the hypervisor and is waiting for the
/// response.
#[derive(PartialEq)]
pub enum PendingRequest {
    SharePage(SharePageRequest),
    GuestLoadPageFault(GuestLoadPageFaultRequest),
    GuestStorePageFault(GuestStorePageFaultRequest),
    SbiRequest(),
}

/// A request send from one confidential hart to another confidential hart belonging to the same confidential VM.
#[derive(Debug, PartialEq, Clone)]
pub enum InterHartRequest {
    SbiHsmHartStart(SbiHsmHartStart),
    InterProcessorInterrupt(SbiIpi),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
}

impl InterHartRequest {
    pub fn into_expose_to_confidential_vm(self) -> ExposeToConfidentialVm {
        match self {
            Self::InterProcessorInterrupt(v) => ExposeToConfidentialVm::InterProcessorInterrupt(v),
            Self::SbiHsmHartStart(v) => ExposeToConfidentialVm::SbiHsmHartStart(v),
            Self::SbiRemoteFenceI(v) => ExposeToConfidentialVm::SbiRemoteFenceI(v),
            Self::SbiRemoteSfenceVma(v) => ExposeToConfidentialVm::SbiRemoteSfenceVma(v),
            Self::SbiRemoteSfenceVmaAsid(v) => ExposeToConfidentialVm::SbiRemoteSfenceVmaAsid(v),
        }
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        match self {
            Self::InterProcessorInterrupt(v) => Self::check_if_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
            Self::SbiHsmHartStart(v) => hart_id == v.confidential_hart_id,
            Self::SbiRemoteFenceI(v) => Self::check_if_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
            Self::SbiRemoteSfenceVma(v) => Self::check_if_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
            Self::SbiRemoteSfenceVmaAsid(v) => Self::check_if_hart_selected(hart_id, v.hart_mask, v.hart_mask_base),
        }
    }

    fn check_if_hart_selected(hart_id: usize, hart_mask: usize, hart_mask_base: usize) -> bool {
        if hart_mask_base == usize::MAX {
            // all harts are selected
            return true;
        }
        let Some(id) = hart_id.checked_sub(hart_mask_base) else {
            return false;
        };
        if id >= usize::BITS as usize {
            return false;
        }
        hart_mask & (1 << id) != 0
    }
}
