// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
pub use base_extension::*;
pub use covg_extension::*;
pub use covh_extension::*;
pub use covi_extension::*;
pub use hsm_extension::*;
pub use ipi_extension::*;
pub use nacl_extension::*;
pub use rfence_extension::*;
pub use spec::*;
pub use srst_extension::*;

mod base_extension;
mod covg_extension;
mod covh_extension;
mod covi_extension;
mod hsm_extension;
mod ipi_extension;
mod nacl_extension;
mod rfence_extension;
mod spec;
mod srst_extension;

#[derive(Debug)]
pub enum SbiExtension {
    Base(BaseExtension),
    Ipi(IpiExtension),
    Rfence(RfenceExtension),
    Hsm(HsmExtension),
    Srst(SrstExtension),
    Nacl(NaclExtension),
    Covh(CovhExtension),
    Covi(CoviExtension),
    Covg(CovgExtension),
    Unknown(usize, usize),
}

impl SbiExtension {
    pub fn decode(a7: usize, a6: usize) -> Self {
        match (a7, a6) {
            (BaseExtension::EXTID, function_id) => Self::Base(BaseExtension::from_function_id(function_id)),
            (IpiExtension::EXTID, function_id) => Self::Ipi(IpiExtension::from_function_id(function_id)),
            (RfenceExtension::EXTID, function_id) => Self::Rfence(RfenceExtension::from_function_id(function_id)),
            (HsmExtension::EXTID, function_id) => Self::Hsm(HsmExtension::from_function_id(function_id)),
            (SrstExtension::EXTID, function_id) => Self::Srst(SrstExtension::from_function_id(function_id)),
            (NaclExtension::EXTID, function_id) => Self::Nacl(NaclExtension::from_function_id(function_id)),
            (CovhExtension::EXTID, function_id) => Self::Covh(CovhExtension::from_function_id(function_id)),
            (CoviExtension::EXTID, function_id) => Self::Covi(CoviExtension::from_function_id(function_id)),
            (CovgExtension::EXTID, function_id) => Self::Covg(CovgExtension::from_function_id(function_id)),
            (extension_id, function_id) => Self::Unknown(extension_id, function_id),
        }
    }
}
