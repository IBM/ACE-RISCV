// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::{MmioLoadPending, MmioStorePending};
use crate::confidential_flow::handlers::shared_page::SharePageRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::SbiHsmHartResume;

/// Indicates an intermediate state of the confidential hart that requested certain operation from the hypervisor and is waiting for the
/// response. This structure might store some information required to complete the request once the hypervisor responds to it.
pub enum PendingRequest {
    SbiRequest(),
    ResumeHart(SbiHsmHartResume),
    SharePage(SharePageRequest),
    MmioLoad(MmioLoadPending),
    MmioStore(MmioStorePending),
}
