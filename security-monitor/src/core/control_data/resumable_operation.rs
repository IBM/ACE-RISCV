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
    SbiRequest(),
    /// Indicates that the confidential hart is suspended and must be resumed once the confidential hart is run again, see hart lifecycle
    /// states.
    ResumeHart(SbiHsmHartResume),
    /// The confidential hart waits for a shared page to be mapped into its address space. The hypervisor must allocate a shared page in
    /// the non-confidential memory.
    SharePage(SharePageRequest),
    /// The confidential hart waits for the data it tried to load from the MMIO address. MMIO load is emulated by the hypervisor.
    MmioLoad(MmioLoadPending),
    /// The confidential hart waits for the data to be stored in the MMIO address. MMIO store is emulated by the hypervisor.
    MmioStore(MmioStorePending),
}
