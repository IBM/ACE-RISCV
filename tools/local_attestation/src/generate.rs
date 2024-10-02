// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::ensure;
use crate::error::Error;
use sha2::Digest;
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
    kernel_file: String,
    kernel_commandline: String,
    initramfs_file: String,
    confidential_vm_secrets: Vec<(usize, String)>,
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
    digests.push(TapDigest {
        entry_type: TapDigestEntryType::Kernel,
        algorithm: TapDigestAlgorithm::Sha512,
        value: measure_file_integrity(kernel_file)?,
    });
    digests.push(TapDigest {
        entry_type: TapDigestEntryType::KernelCommandLine,
        algorithm: TapDigestAlgorithm::Sha512,
        value: measure_string_integrity(kernel_commandline)?,
    });
    digests.push(TapDigest {
        entry_type: TapDigestEntryType::Initramfs,
        algorithm: TapDigestAlgorithm::Sha512,
        value: measure_file_integrity(initramfs_file)?,
    });

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
        .write(true)
        .append(false)
        .open(output_file.clone())
        .map_err(|_| Error::CannotOpenFile(output_file))?;
    output.write(&serialized)?;

    Ok(())
}

fn measure_file_integrity(file: String) -> Result<Vec<u8>, Error> {
    let mut hasher = sha2::Sha512::new();
    let mut file =
        std::fs::File::open(file.clone()).map_err(|_| Error::CannotOpenFile(file.clone()))?;
    std::io::copy(&mut file, &mut hasher)?;
    let digest = hasher.finalize();
    println!("Measured file {:?}, digest={:?}", file, digest);
    Ok(digest.to_vec())
}

fn measure_string_integrity(value: String) -> Result<Vec<u8>, Error> {
    let mut hasher = sha2::Sha512::new();
    hasher.update(value.as_bytes());
    Ok(hasher.finalize().to_vec())
}
