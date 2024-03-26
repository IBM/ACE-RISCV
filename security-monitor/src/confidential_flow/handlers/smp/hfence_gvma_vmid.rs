// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::smp::SbiIpi;
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::PageSize;

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteHfenceGvmaVmid {
    ipi: SbiIpi,
    start_address: usize,
    size: PageSize,
    vmid: ConfidentialVmId,
}

impl SbiRemoteHfenceGvmaVmid {
    pub fn new(
        hart_mask: usize, hart_mask_base: usize, start_address: &ConfidentialVmPhysicalAddress, size: PageSize, vmid: ConfidentialVmId,
    ) -> Self {
        Self { ipi: SbiIpi::new(hart_mask, hart_mask_base), start_address: start_address.usize(), size, vmid }
    }

    pub fn all_harts(start_address: &ConfidentialVmPhysicalAddress, size: PageSize, vmid: ConfidentialVmId) -> Self {
        Self::new(usize::MAX, usize::MAX, start_address, size, vmid)
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_gvma();
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}
