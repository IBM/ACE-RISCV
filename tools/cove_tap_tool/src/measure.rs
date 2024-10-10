// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use std::fs::OpenOptions;

use sha2::digest::crypto_common::generic_array::GenericArray;
pub type DigestType = sha2::Sha384;
pub type MeasurementDigest =
    GenericArray<u8, <DigestType as sha2::digest::OutputSizeUser>::OutputSize>;

pub fn measure(kernel_file: String) -> Result<(), Error> {
    use std::io::BufReader;
    use std::io::Read;

    let mut digest = MeasurementDigest::default();

    let kernel = OpenOptions::new().read(true).open(kernel_file)?;
    let mut buf = BufReader::new(kernel);
    let mut buffer = [0u8; 4096]; // 1 4KiB page
    let mut address = 0x80000000 as u64;
    while let Ok(bytes_read) = buf.read(&mut buffer) {
        if bytes_read == 0 {
            break;
        }
        let header = [buffer[0], buffer[1], buffer[2], buffer[3]];
        if u32::from_le_bytes(header) == tap::ACE_MAGIC_TAP_START {
            (0..4096).for_each(|i| buffer[i] = 0); // security monitor will clear it
        }
        if buffer.iter().find(|b| **b != 0).is_some() {
            use sha2::Digest;
            let mut hasher = DigestType::new_with_prefix(digest.clone());
            hasher.update(address.to_le_bytes());
            hasher.update(&buffer);
            hasher.finalize_into(&mut digest);
            println!("Page 0x{:x} {:100x}", address, digest);
        } else {
            // println!("Page 0x{:x} empty", address);
        }
        address += 4096;
        (0..4096).for_each(|i| buffer[i] = 0);
    }
    println!("Digest {:100x}", digest);
    Ok(())
}
