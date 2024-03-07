// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub fn tlb_shutdown() {
    // TODO: implement TLB shutdown for a processor composed of multiple HARTs
    crate::core::architecture::hfence_gvma();
    crate::core::architecture::hfence_vvma();
}
