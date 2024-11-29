// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use byteorder::WriteBytesExt;
use std::fs::OpenOptions;
use std::io::BufReader;
use std::io::Read;
use std::io::Seek;
use std::io::SeekFrom;

pub fn attach_tap(
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
    let offset = find_placehoder(&output_file_name)?;
    // clear the placeholder
    let mut output_file = OpenOptions::new().write(true).open(output_file_name)?;
    output_file.seek(SeekFrom::Start(offset))?;
    (riscv_cove_tap::ACE_HEADER_SIZE..riscv_cove_tap::ACE_MAX_TAP_SIZE).try_for_each(|_| output_file.write_u8(0u8))?;
    // write expected TAP from the beginning of the offset
    output_file.seek(SeekFrom::Start(offset))?;
    let mut tap_file = OpenOptions::new().read(true).open(tap_file_name)?;
    std::io::copy(&mut tap_file, &mut output_file)?;
    println!("TAP attached successfully");
    Ok(())
}

fn find_placehoder(output_file_name: &str) -> Result<u64, Error> {
    let output_file = OpenOptions::new().read(true).open(output_file_name)?;
    let mut buf = BufReader::new(output_file);
    let mut buffer = [0u8; 4];
    let mut offset = 0u64;
    while let Ok(bytes_read) = buf.read(&mut buffer) {
        if bytes_read == 0 {
            break;
        }
        if u32::from_le_bytes(buffer) == riscv_cove_tap::ACE_MAGIC_TAP_START {
            println!("Found TAP placeholder at offset: {:x}", offset);
            return Ok(offset);
        }
        offset += bytes_read as u64;
    }
    Err(Error::PlaceholderError())
}
