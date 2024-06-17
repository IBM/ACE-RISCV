// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use sha2::digest::crypto_common::generic_array::GenericArray;

pub type DigestType = sha2::Sha384;
pub type MeasurementDigest = GenericArray<u8, <DigestType as sha2::digest::OutputSizeUser>::OutputSize>;

/// Number of registers storing boottime integrity measurements. CoVE spec requires at least 1 and maximum 8.
const NUMBER_OF_REGISTERS: usize = 8;
/// The number of the register that stores the measurement of confidential VM code and static data
const TVM_CODE_AND_STATIC_DATA_REGISTER_ID: usize = 4;
/// The number of the register that stores the measurement of confidential boot hart state
const TVM_CONFIGURATION_REGISTER_ID: usize = 5;

pub struct StaticMeasurements([MeasurementDigest; NUMBER_OF_REGISTERS]);

impl StaticMeasurements {
    pub fn new(measured_pages: MeasurementDigest, configuration: MeasurementDigest) -> Self {
        let mut measurements = Self([MeasurementDigest::default(); NUMBER_OF_REGISTERS]);
        measurements.0[TVM_CODE_AND_STATIC_DATA_REGISTER_ID] = measured_pages;
        measurements.0[TVM_CONFIGURATION_REGISTER_ID] = configuration;
        measurements
    }
}

impl core::fmt::Debug for StaticMeasurements {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.iter().enumerate().for_each(|(id, value)| {
            let _ = write!(f, "\nPCR{}={:100x}", id, value);
        });
        write!(f, "")
    }
}
