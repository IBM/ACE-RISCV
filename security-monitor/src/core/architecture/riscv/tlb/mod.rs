// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub fn clear_hart_tlbs() {
    super::fence::hfence_gvma();
    super::fence::hfence_vvma();
}
