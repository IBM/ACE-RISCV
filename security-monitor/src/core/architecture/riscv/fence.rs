// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]

pub fn fence_wo() {
    unsafe { core::arch::asm!("fence w,o") };
}

pub fn hfence_gvma() {
    unsafe { core::arch::asm!("hfence.gvma") };
}

pub fn hfence_vvma() {
    unsafe { core::arch::asm!("hfence.vvma") };
}

pub fn sfence_vma() {
    unsafe { core::arch::asm!("sfence.vma") };
}

pub fn fence_i() {
    unsafe { core::arch::asm!("fence.i") };
}
