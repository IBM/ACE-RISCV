// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;

#[derive(Debug)]
pub struct ConfidentialVmMmioRegion {
    pub region_start_address: usize,
    pub region_length: usize,
}

impl ConfidentialVmMmioRegion {
    pub fn new(region_start_address: usize, region_length: usize) -> Result<Self, Error> {
        // TODO: make sure region_start_address is aligned to 4KiB
        // TODO: make sure the region_start_address is a valid guest address
        Ok(Self { region_start_address, region_length })
    }

    pub fn overlaps(&self, other: &Self) -> bool {
        self.region_start_address < other.region_start_address + other.region_length
            && other.region_start_address < self.region_start_address + self.region_length
    }

    pub fn contains(&self, other: &Self) -> bool {
        self.region_start_address <= other.region_start_address
            && other.region_start_address + other.region_length < self.region_start_address + self.region_length
    }
}
