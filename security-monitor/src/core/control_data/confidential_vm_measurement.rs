// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use generic_array::GenericArray;

pub type DigestType = sha3::Sha3_384;
pub type MeasurementDigest = GenericArray<u8, <DigestType as sha3::digest::OutputSizeUser>::OutputSize>;

/// Number of registers storing boottime integrity measurements. CoVE spec requires at least 1 and maximum 8.
const NUMBER_OF_REGISTERS: usize = 8;
/// The number of the register that stores the measurement of confidential VM code and static data
const KERNEL_PCR_ID: usize = 4;
/// The number of the register that stores the measurement of confidential VM code and static data
const INITRD_PCR_ID: usize = 5;
/// The number of the register that stores the measurement of confidential VM code and static data
const FDT_PCR_ID: usize = 6;
/// The number of the register that stores the measurement of confidential boot hart state
const BOOT_HART_PCR_ID: usize = 7;

pub struct StaticMeasurements([MeasurementDigest; NUMBER_OF_REGISTERS]);

impl StaticMeasurements {
    pub fn default() -> Self {
        Self([MeasurementDigest::default(); NUMBER_OF_REGISTERS])
    }

    pub fn compare(&self, pcr_id: usize, digest: MeasurementDigest) -> Result<bool, Error> {
        ensure!(pcr_id < NUMBER_OF_REGISTERS, Error::InvalidParameter())?;
        Ok(self.0[pcr_id] == digest)
    }

    pub fn pcr_kernel_mut(&mut self) -> &mut MeasurementDigest {
        &mut self.0[KERNEL_PCR_ID]
    }

    pub fn pcr_initrd_mut(&mut self) -> &mut MeasurementDigest {
        &mut self.0[INITRD_PCR_ID]
    }

    pub fn pcr_fdt_mut(&mut self) -> &mut MeasurementDigest {
        &mut self.0[FDT_PCR_ID]
    }

    pub fn pcr_boot_hart_mut(&mut self) -> &mut MeasurementDigest {
        &mut self.0[BOOT_HART_PCR_ID]
    }
}

#[rr::skip]
impl core::fmt::Debug for StaticMeasurements {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.iter().enumerate().for_each(|(id, value)| {
            let _ = write!(f, "\nPCR{}={:100x}", id, value);
        });
        write!(f, "")
    }
}
