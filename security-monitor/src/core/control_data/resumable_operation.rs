// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::{MmioLoadPending, MmioStorePending};
use crate::confidential_flow::handlers::shared_page::SharePageRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::SbiHsmHartResume;

/// Indicates an intermediate state of the confidential hart that requested certain operation from the hypervisor and is waiting for the
/// response. Thus, the hypervisor must provide the response when resuming execution of this confidential hart.
///
/// The security monitor uses information persisted in this structure to complete the operation, which was initiated by the confidential
/// hart.
pub enum ResumableOperation {
    /// The confidential hart performed an SBI call (hypercall) and now is waiting for the hypervisor to perform handle this operation.
    SbiRequest(),
    /// The confidential hart requested to be suspended and expects to be reset on next resume, see hart lifecycle states.
    ResumeHart(SbiHsmHartResume),
    /// The confidential hart requested to share memory range with the hypervisor and now is waiting for a shared page to be mapped into
    /// its address space.
    SharePage(SharePageRequest),
    /// The confidential hart requested to load data from a MMIO address and is waiting for the hypervisor to emulate this operation.
    MmioLoad(MmioLoadPending),
    /// The confidential hart requested to store data in a MMIO address and now is waiting for the hypervisor to emulate this operation.
    MmioStore(MmioStorePending),
}
