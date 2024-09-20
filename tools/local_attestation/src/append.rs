// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use byteorder::{LittleEndian, WriteBytesExt};
use std::fs::OpenOptions;

pub fn append_tap(
    input_file: String,
    tap_file: String,
    output_file: Option<String>,
) -> Result<(), Error> {
    let output_file_name = match output_file {
        Some(f) if input_file != f => {
            std::fs::copy(input_file, f.clone())?;
            f
        }
        Some(f) => f,
        None => input_file,
    };
    let mut file1 = OpenOptions::new()
        .write(true)
        .append(true)
        .open(output_file_name)?;
    let mut file2 = OpenOptions::new().read(true).open(tap_file)?;
    let tap_size_in_bytes = std::io::copy(&mut file2, &mut file1)?;
    file1
        .write_u32::<LittleEndian>(crate::constants::ACE_TAP_MAGIC)
        .unwrap();
    file1
        .write_u16::<LittleEndian>(tap_size_in_bytes.try_into().unwrap())
        .unwrap();
    Ok(())
}
