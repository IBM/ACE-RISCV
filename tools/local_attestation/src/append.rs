// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use byteorder::WriteBytesExt;
use std::fs::OpenOptions;
use std::io::Seek;
use std::io::SeekFrom;

pub fn append_tap(
    input_file: String,
    tap_file_name: String,
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
    let output_file_size = file_size(&output_file_name)?;

    let mut output_file = OpenOptions::new()
        .write(true)
        .append(true)
        .open(output_file_name)?;

    // TAP must be 8-bytes aligned
    let mut aligned = (output_file_size >> 3) << 3;
    if aligned < output_file_size {
        aligned = ((output_file_size >> 3) + 1) << 3;
    }
    let padding_size_in_bytes = aligned - output_file_size;
    for _ in 0..padding_size_in_bytes {
        output_file.write_u8(0u8)?;
    }

    let mut tap_file = OpenOptions::new().read(true).open(tap_file_name)?;
    std::io::copy(&mut tap_file, &mut output_file)?;
    Ok(())
}

fn file_size(file_name: &str) -> Result<u64, Error> {
    Ok(OpenOptions::new()
        .read(true)
        .open(file_name)?
        .seek(SeekFrom::End(0))?)
}
