// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use byteorder::{LittleEndian, WriteBytesExt};
use std::io::{Write};
use std::fs::OpenOptions;
use sha2::{Digest};
use rand::RngCore;
// use hex_literal::hex;

use crate::constants::TapDigestAlgorithm;
use crate::constants::TapDigestEntryType;
use crate::constants::TapLockboxAlgorithm;

pub fn generate_tap(kernel_file: String, kernel_commandline: String, initramfs_file: String, confidential_vm_secrets: Vec<(usize, String)>, tee_public_keys_files: Vec<String>, output_file: String) -> Result<(), Error> {
    // Sanity check:
    // - number of secrets must be lower than 256
    if confidential_vm_secrets.len() >= 256 {
        return Err(Error::InvalidParameter(format!("Confidential VM can receive maximum 256 secrets")));
    }
    // - number of lockboxes must be lower than 1024
    if tee_public_keys_files.len() >= 1024 {
        return Err(Error::InvalidParameter(format!("Confidential VM TAP support max 1024 lockboxes")));
    }

    // symmetric key will be used to encrypt payload and calculate hmac
    let mut symmetric_key = [0u8; 32];
    rand::thread_rng().fill_bytes(&mut symmetric_key);

    // generate lockboxes
    let mut lockboxes = vec![];
    // number of lock boxes
    lockboxes.write_u16::<LittleEndian>(tee_public_keys_files.len().try_into()?)?;
    for public_key_file in tee_public_keys_files.iter() {
        // lock box entry: entry size; algorithm; ciphertext
        let mut ciphertext = encrypt_rsa_2048_sha256_oasp(&symmetric_key, public_key_file.to_string())?;
        lockboxes.write_u16::<LittleEndian>((8 + ciphertext.len()) as u16)?;
        lockboxes.write_u8(TapLockboxAlgorithm::Rsa_2048_Sha256_OASP as u8)?;
        lockboxes.append(&mut ciphertext);
    }
    
    let mut payload = vec![];
    // number of digests
    payload.write_u8(3)?;
    // first digest: entry size; entry type; algorithm; digest 
    payload.write_u16::<LittleEndian>(2+TapDigestAlgorithm::Sha512.digest_size())?;
    payload.write_u8(TapDigestEntryType::Kernel as u8)?;
    payload.write_u8(TapDigestAlgorithm::Sha512 as u8)?;
    payload.append(&mut measure_file_integrity(kernel_file)?);
    // second digest
    payload.write_u16::<LittleEndian>(2+TapDigestAlgorithm::Sha512.digest_size())?;
    payload.write_u8(TapDigestEntryType::KernelCommandLine as u8)?;
    payload.write_u8(TapDigestAlgorithm::Sha512 as u8)?;
    payload.append(&mut measure_string_integrity(kernel_commandline)?);
    // third digest
    payload.write_u16::<LittleEndian>(2+TapDigestAlgorithm::Sha512.digest_size())?;
    payload.write_u8(TapDigestEntryType::Initramfs as u8)?;
    payload.write_u8(TapDigestAlgorithm::Sha512 as u8)?;
    payload.append(&mut measure_file_integrity(initramfs_file)?);
    // number of confidential VM's secrets
    payload.write_u8(confidential_vm_secrets.len().try_into()?)?;
    for (key, value) in confidential_vm_secrets.iter() {
        // each confidential VM's secret entry consist of: entry size; key; value
        payload.write_u16::<LittleEndian>((8 + value.as_bytes().len()) as u16)?;
        payload.write_u64::<LittleEndian>(*key as u64)?;
        payload.append(&mut value.as_bytes().to_vec());
    }
    // payload's HMAC
    let mut payload_hmac = hmac_sha512(&symmetric_key, &payload)?;

    // encrypt payload and hmac
    let mut serialized_payload_and_hmac = vec![];
    serialized_payload_and_hmac.write_u16::<LittleEndian>(payload.len().try_into()?)?;
    serialized_payload_and_hmac.append(&mut payload);
    serialized_payload_and_hmac.write_u16::<LittleEndian>(payload_hmac.len().try_into()?)?;
    serialized_payload_and_hmac.append(&mut payload_hmac);

    use aes_gcm::{Aes256Gcm, KeyInit, AeadInPlace, Key, AeadCore};
    use rand::rngs::OsRng;
    let key: Key<Aes256Gcm> = symmetric_key.into();
    let cipher = Aes256Gcm::new(&key);
    let nonce = Aes256Gcm::generate_nonce(&mut OsRng);
    cipher.encrypt_in_place(&nonce, b"", &mut serialized_payload_and_hmac).unwrap();

    // write the entire TAP to the output file
    let mut output = OpenOptions::new().create_new(true).write(true).append(false).open(output_file.clone()).map_err(|_| Error::CannotOpenFile(output_file))?;
    output.write(&lockboxes)?;
    output.write(&serialized_payload_and_hmac)?;

    Ok(())
}

fn encrypt_rsa_2048_sha256_oasp(value: &[u8], public_key_file: String) -> Result<Vec<u8>, Error> {
    use rsa::pkcs1::DecodeRsaPublicKey;
    let public_key_pem: Vec<u8> = std::fs::read(public_key_file.clone()).map_err(|_| Error::CannotOpenFile(public_key_file))?;
    let public_key = rsa::RsaPublicKey::from_pkcs1_pem(&String::from_utf8_lossy(&public_key_pem))?;
    let padding = rsa::Oaep::new::<sha2::Sha256>();
    let encrypted_data = public_key.encrypt(&mut rand::thread_rng(), padding, value)?;
    Ok(encrypted_data)
}

fn hmac_sha512(hmac_key: &[u8], payload: &[u8]) -> Result<Vec<u8>, Error> {
    use hmac::{Mac};
    let mut hmac = hmac::Hmac::<sha2::Sha512>::new_from_slice(hmac_key).map_err(|_| Error::InvalidSizeOfSymmetricKey())?;
    hmac.update(payload);
    Ok(hmac.finalize().into_bytes().to_vec())
}

fn measure_file_integrity(file: String) -> Result<Vec<u8>, Error> {
    let mut hasher = sha2::Sha512::new();
    let mut file = std::fs::File::open(file.clone()).map_err(|_| Error::CannotOpenFile(file.clone()))?;
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