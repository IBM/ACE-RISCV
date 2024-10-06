// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::ensure;
use crate::error::Error;
use std::fs::OpenOptions;
use std::io::Write;

use tap::Lockbox;
use tap::TapDigest;
use tap::TapDigestAlgorithm;
use tap::TapDigestEntryType;
use tap::TapLockboxAlgorithm;
use tap::TapSecret;
use tap::TeeAttestationPayload;
use tap::TeeAttestationPayloadSerializer;

pub fn generate_tap(
    pcrs: Vec<(u16, Vec<u8>)>,
    confidential_vm_secrets: Vec<(usize, Vec<u8>)>,
    tee_public_keys_files: Vec<String>,
    output_file: String,
) -> Result<(), Error> {
    ensure!(
        confidential_vm_secrets.len() < 256,
        Error::InvalidParameter(format!("Confidential VM can receive maximum 256 secrets"))
    )?;
    ensure!(
        tee_public_keys_files.len() < 1024,
        Error::InvalidParameter(format!("Confidential VM TAP support max 1024 lockboxes"))
    )?;

    // let symmetric_key = [0u8; 32];

    let mut lockboxes = vec![];
    lockboxes.push(Lockbox {
        name: 0u64,
        algorithm: TapLockboxAlgorithm::Debug,
        value: [0xFF; 16].to_vec(),
    });

    let mut digests = vec![];
    for (pcr_number, pcr_value) in pcrs.into_iter() {
        let tap_digest = TapDigest {
            entry_type: TapDigestEntryType::from_u16(pcr_number)?,
            algorithm: TapDigestAlgorithm::Sha512,
            value: pcr_value,
        };
        println!("Writing PCR{}={}", pcr_number, tap_digest.value_in_hex());
        digests.push(tap_digest);
    }

    let mut secrets = vec![];
    secrets.push(TapSecret {
        name: 0,
        value: [0xFF; 16].to_vec(),
    });

    let tap = TeeAttestationPayload {
        lockboxes,
        digests,
        secrets,
    };

    let serializer = TeeAttestationPayloadSerializer::new();
    let serialized = serializer.serialize(tap)?;

    // write the entire TAP to the output file
    let mut output = OpenOptions::new()
        .create_new(true)
        .read(true)
        .write(true)
        .append(false)
        .open(output_file.clone())
        .map_err(|_| Error::CannotOpenFile(output_file.clone()))?;
    output.write(&serialized)?;

    // test if everything went well
    use std::io::Read;
    use std::io::{Seek, SeekFrom};
    output.seek(SeekFrom::End(-1 * (serialized.len() as i64)))?;
    let mut test_data: Vec<u8> = vec![0u8; serialized.len()];
    output.read_exact(&mut test_data)?;
    let mut parser = tap::TeeAttestationPayloadParser::from_raw_pointer(
        test_data.as_mut_ptr() as *const u8,
        test_data.len() - 4,
    )?;
    let tap = parser.parse_and_verify()?;
    for digest in tap.digests.iter() {
        println!(
            "Read PCR{}={}",
            digest.entry_type.to_u16(),
            digest.value_in_hex()
        );
    }

    Ok(())
}
