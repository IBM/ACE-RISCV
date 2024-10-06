// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use byteorder::WriteBytesExt;
use std::fs::OpenOptions;
use std::io::Read;
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
    let mut output_file_size = file_size(&output_file_name)?;

    let mut output_file = OpenOptions::new()
        .read(true)
        .write(true)
        .append(true)
        .open(output_file_name)?;

    // check first if there is a TAP already appended
    output_file.seek(SeekFrom::End(-4))?;
    let mut footer = [0u8; 4];
    output_file.read_exact(&mut footer)?;
    if u16::from_le_bytes([footer[0], footer[1]]) == tap::spec::ACE_MAGIC_TAP_END {
        println!("Removing old TAP");
        let old_tap_size = u16::from_le_bytes([footer[2], footer[3]]) as u64;
        output_file.set_len(output_file_size - old_tap_size)?;
        output_file.seek(SeekFrom::End(0))?;
        output_file_size -= old_tap_size;
    }

    // TAP must be 8-bytes aligned
    let mut aligned = (output_file_size >> 3) << 3;
    if aligned < output_file_size {
        aligned = ((output_file_size >> 3) + 1) << 3;
    }
    let padding_size_in_bytes = aligned - output_file_size;
    println!(
        "Padding with {} bytes to align to u64",
        padding_size_in_bytes
    );
    (0..padding_size_in_bytes).try_for_each(|_| output_file.write_u8(0u8))?;

    let mut tap_file = OpenOptions::new().read(true).open(tap_file_name)?;
    std::io::copy(&mut tap_file, &mut output_file)?;

    println!("TAP appended successfully");
    Ok(())
}

fn file_size(file_name: &str) -> Result<u64, Error> {
    Ok(OpenOptions::new()
        .read(true)
        .open(file_name)?
        .seek(SeekFrom::End(0))?)
}
