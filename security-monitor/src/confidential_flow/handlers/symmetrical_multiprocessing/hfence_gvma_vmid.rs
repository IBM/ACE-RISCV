// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::symmetrical_multiprocessing::SbiIpi;
use crate::core::control_data::{ConfidentialHart, ConfidentialHartRemoteCommandExecutable, ConfidentialVmId};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::PageSize;

/// An inter hart request sent by the security monitor to clear G-stage level cached address translations.
#[derive(Clone)]
pub struct SbiRemoteHfenceGvmaVmid {
    ipi: SbiIpi,
    _start_address: usize,
    _size: PageSize,
    _vmid: ConfidentialVmId,
}

impl SbiRemoteHfenceGvmaVmid {
    pub fn all_harts(start_address: &ConfidentialVmPhysicalAddress, _size: PageSize, _vmid: ConfidentialVmId) -> Self {
        Self { ipi: SbiIpi::all_harts(), _start_address: start_address.usize(), _size, _vmid }
    }
}

impl ConfidentialHartRemoteCommandExecutable for SbiRemoteHfenceGvmaVmid {
    fn execute_on_confidential_hart(&self, _confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_gvma();
    }

    fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}
