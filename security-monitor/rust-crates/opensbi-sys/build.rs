// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
extern crate bindgen;

use std::env;
use std::path::{Path, PathBuf};

static INSTALL_DIR: &str = "INSTALL_DIR";

fn main() {
    let install_dir = match env::var(INSTALL_DIR) {
        Ok(v) => v,
        Err(_) => panic!("You must define {} pointing to the opensbi installation (library and headers)", INSTALL_DIR)
    };

    let lib_dir = format!("{}/opensbi-rust-bindings/lib", install_dir);
    if !Path::new(&lib_dir).exists() {
        panic!("The directory with library does not exist: {}. Specify the environmental variable {} and check {}/opensbi", lib_dir, INSTALL_DIR, install_dir);
    }
 
    let include_dir = format!("{}/opensbi-rust-bindings/include", install_dir);
    if !Path::new(&include_dir).exists() {
        panic!("The directory with headers does not exist: {}", include_dir);
    }
 
    println!("cargo:rustc-link-search=native={}", lib_dir);
    println!("cargo:rustc-link-lib={}={}", "dylib", "sbi");
    println!("cargo:include={}", include_dir);
 
    let bindings = bindgen::Builder::default()
        .header("src/wrapper.h")
        .clang_arg(format!("-I{}", include_dir)) 
        .ctypes_prefix("core::ffi")
        .derive_debug(true)
        .derive_default(true)
        .use_core()
        .generate()
        .expect("Unable to generate bindings");

        
    let out_path = PathBuf::from(env::var("OUT_DIR").expect("Couldn't create output directory"));
    bindings.write_to_file(out_path.join("bindings.rs")).expect("Couldn't write bindings!");
}