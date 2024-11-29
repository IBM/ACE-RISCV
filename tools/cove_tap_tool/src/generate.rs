// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::ensure;
use crate::error::Error;
use std::fs::OpenOptions;
use std::io::Write;
use riscv_cove_tap::AttestationPayload;
use riscv_cove_tap::AttestationPayloadSerializer;
use riscv_cove_tap::Digest;
use riscv_cove_tap::DigestAlgorithm;
use riscv_cove_tap::Lockbox;
use riscv_cove_tap::LockboxAlgorithm;
use riscv_cove_tap::Secret;

pub fn generate_tap(
    pcrs: Vec<(u16, Vec<u8>)>,
    confidential_vm_secrets: Vec<(u64, Vec<u8>)>,
    tee_public_keys_files: Vec<String>,
    output_file: String,
) -> Result<(), Error> {
    ensure!(
        confidential_vm_secrets.len() < 256,
        Error::InvalidParameter(format!("Confidential VM can receive maximum 256 secrets"))
    )?;
    ensure!(
        tee_public_keys_files.len() < 1024,
        Error::InvalidParameter(format!("Confidential VM TAP supports max 1024 lockboxes"))
    )?;

    // let symmetric_key = [0u8; 32];

    let mut lockboxes = vec![];
    lockboxes.push(Lockbox {
        name: 0u64,
        algorithm: LockboxAlgorithm::Debug,
        value: [0xFF; 16].to_vec(),
    });

    let mut digests = vec![];
    for (pcr_id, pcr_value) in pcrs.into_iter() {
        let tap_digest = Digest {
            pcr_id,
            algorithm: DigestAlgorithm::Sha512,
            value: pcr_value,
        };
        println!("Writing PCR{}={}", pcr_id, tap_digest.value_in_hex());
        digests.push(tap_digest);
    }

    let mut secrets = vec![];
    for (secret_name, secret_value) in confidential_vm_secrets.into_iter() {
        let secret = Secret {
            name: secret_name,
            value: secret_value,
        };
        println!("Writing secret {}", secret_name);
        secrets.push(secret);
    }

    let tap = AttestationPayload {
        lockboxes,
        digests,
        secrets,
    };

    let serializer = AttestationPayloadSerializer::new();
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

    Ok(())
}
