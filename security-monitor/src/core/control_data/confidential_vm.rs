// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, HardwareHart};
use crate::core::mmu::RootPageTable;
use crate::error::Error;
use alloc::vec::Vec;
use riscv::register::hgatp::Hgatp;

const MAX_HASH_SIZE: usize = 512; // 512b for SHA-512

#[derive(PartialEq, Eq, Hash, Debug, PartialOrd, Ord, Copy, Clone)]
pub struct ConfidentialVmId(usize);

impl ConfidentialVmId {
    pub fn new(value: usize) -> Self {
        Self(value)
    }
    pub fn usize(&self) -> usize {
        self.0
    }
}

pub struct ConfidentialVm {
    id: ConfidentialVmId,
    _measurements: [Measurement; 4],
    confidential_harts: Vec<ConfidentialHart>,
    root_page_table: RootPageTable,
}

impl ConfidentialVm {
    pub fn new(
        id: ConfidentialVmId, mut confidential_harts: Vec<ConfidentialHart>, root_page_table: RootPageTable,
    ) -> Self {
        let hgatp = Hgatp::new(root_page_table.address().usize(), root_page_table.paging_system().hgatp_mode(), id.0);
        confidential_harts.iter_mut().for_each(|confidential_hart| confidential_hart.set_hgatp(hgatp.bits()));
        Self { id, _measurements: [Measurement::empty(); 4], confidential_harts, root_page_table }
    }

    pub fn root_page_table_mut(&mut self) -> &mut RootPageTable {
        &mut self.root_page_table
    }

    pub fn steal_confidential_hart(
        &mut self, confidential_hart_id: usize, hardware_hart: &mut HardwareHart,
    ) -> Result<(), Error> {
        let confidential_hart = self.confidential_harts.get(confidential_hart_id).ok_or(Error::InvalidHartId())?;
        // The hypervisor might try to schedule the same confidential_hart on different harts. We detect it because
        // after a confidential_hart is scheduled for the first time, its token is stolen and the ConfidentialVM is left
        // with a dummy confidential_hart.
        assure_not!(confidential_hart.is_dummy(), Error::RunningVHart())?;
        core::mem::swap(&mut hardware_hart.confidential_hart, &mut self.confidential_harts[confidential_hart_id]);
        Ok(())
    }

    pub fn return_confidential_hart(&mut self, hardware_hart: &mut HardwareHart) {
        assert!(!hardware_hart.confidential_hart.is_dummy());
        assert!(self.id == hardware_hart.confidential_hart().confidential_vm_id());
        let confidential_hart_id = hardware_hart.confidential_hart.confidential_hart_id();
        core::mem::swap(&mut hardware_hart.confidential_hart, &mut self.confidential_harts[confidential_hart_id]);
    }

    pub fn is_running(&self) -> bool {
        self.confidential_harts.iter().filter(|confidential_hart| confidential_hart.is_dummy()).count() > 0
    }
}

#[derive(Clone, Copy)]
pub struct Measurement {
    pub value: [u8; MAX_HASH_SIZE / 8],
}

impl Measurement {
    pub const fn empty() -> Measurement {
        Self { value: [0u8; MAX_HASH_SIZE / 8] }
    }
}
