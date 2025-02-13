// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::ensure;
use crate::error::Error;
use riscv_cove_tap::AttestationPayload;
use riscv_cove_tap::AttestationPayloadSerializer;
use riscv_cove_tap::Digest;
use riscv_cove_tap::DigestAlgorithm;
use riscv_cove_tap::Lockbox;
use riscv_cove_tap::LockboxAlgorithm;
use riscv_cove_tap::Secret;
use std::fs::OpenOptions;
use std::io::Write;

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

    let symmetric_key = vec![0u8; 32];
    let lockbox_algorithm = LockboxAlgorithm::MlKem1024Aes256;
    let test_encapsulation_key = "307A4CEA4148219B958EA0B7886659235A4D1980B192610847D86EF32739F94C3B446C4D81D89B8B422A9D079C88B11ACAF321B014294E18B296E52F3F744CF9634A4FB01DB0D99EF20A633A552E76A0585C6109F018768B763AF3678B4780089C1342B96907A29A1C11521C744C2797D0BF2B9CCDCA614672B45076773F458A31EF869BE1EB2EFEB50D0E37495DC5CA55E07528934F6293C4168027D0E53D07FACC6630CB08197E53FB193A171135DC8AD9979402A71B6926BCDCDC47B93401910A5FCC1A813B682B09BA7A72D2486D6C799516465C14729B26949B0B7CBC7C640F267FED80B162C51FD8E09227C101D505A8FAE8A2D7054E28A78BA8750DECF9057C83979F7ABB084945648006C5B28804F34E73B238111A65A1F500B1CC606A848F2859070BEBA7573179F36149CF5801BF89A1C38CC278415528D03BDB943F96280C8CC52042D9B91FAA9D6EA7BCBB7AB1897A3266966F78393426C76D8A49578B98B159EBB46EE0A883A270D8057CD0231C86906A91DBBADE6B2469581E2BCA2FEA8389F7C74BCD70961EA5B934FBCF9A6590BF86B8DB548854D9A3FB30110433BD7A1B659CA8568085639237B3BDC37B7FA716D482A25B54106B3A8F54D3AA99B5123DA96066904592F3A54EE23A7981AB608A2F4413CC658946C6D7780EA765644B3CC06C70034AB4EB351912E7715B56755D09021571BF340AB92598A24E811893195B96A1629F8041F58658431561FC0AB15292B913EC473F04479BC145CD4C563A286235646CD305A9BE1014E2C7B130C33EB77CC4A0D9786BD6BC2A954BF3005778F8917CE13789BBB962807858B67731572B6D3C9B4B5206FAC9A7C8961698D88324A915186899B29923F08442A3D386BD416BCC9A100164C930EC35EAFB6AB35851B6C8CE6377366A175F3D75298C518D44898933F53DEE617145093379C4659F68583B2B28122666BEC57838991FF16C368DD22C36E780C91A3582E25E19794C6BF2AB42458A8DD7705DE2C2AA20C054E84B3EF35032798626C248263253A71A11943571340A978CD0A602E47DEE540A8814BA06F31414797CDF6049582361BBABA387A83D89913FE4C0C112B95621A4BDA8123A14D1A842FB57B83A4FBAF33A8E552238A596AAE7A150D75DA648BC44644977BA1F87A4C68A8C4BD245B7D00721F7D64E822B085B901312EC37A8169802160CCE1160F010BE8CBCACE8E7B005D7839234A707868309D03784B4273B1C8A160133ED298184704625F29CFA086D13263EE5899123C596BA788E5C54A8E9BA829B8A9D904BC4BC0BBEA76BC53FF811214598472C9C202B73EFF035DC09703AF7BF1BABAAC73193CB46117A7C9492A43FC95789A924C5912787B2E2090EBBCFD3796221F06DEBF9CF70E056B8B9161D6347F47335F3E1776DA4BB87C15CC826146FF0249A413B45AA93A805196EA453114B524E310AEDAA46E3B99642368782566D049A726D6CCA910993AED621D0149EA588A9ABD909DBB69AA22829D9B83ADA2209A6C2659F2169D668B9314842C6E22A74958B4C25BBDCD293D99CB609D866749A485DFB56024883CF5465DBA0363206587F45597F89002FB8607232138E03B2A894525F265370054B48863614472B95D0A2303442E378B0DD1C75ACBAB971A9A8D1281C79613ACEC6933C377B3C578C2A61A1EC181B101297A37CC5197B2942F6A0E4704C0EC63540481B9F159DC255B59BB55DF496AE54217B7689BD51DBA0383A3D72D852FFCA76DF05B66EECCBD47BC53040817628C71E361D6AF889084916B408A466C96E7086C4A60A10FCF7537BB94AFBCC7D437590919C28650C4F2368259226A9BFDA3A3A0BA1B5087D9D76442FD786C6F81C68C0360D7194D7072C4533AEA86C2D1F8C0A27696066F6CFD11003F797270B32389713CFFA093D991B63844C385E72277F166F5A3934D6BB89A4788DE28321DEFC7457AB484BD30986DC1DAB3008CD7B22F69702FABB9A1045407DA4791C3590FF599D81D688CFA7CC12A68C50F51A1009411B44850F9015DC84A93B17C7A207552C661EA9838E31B95EAD546248E56BE7A5130505268771199880A141771A9E47ACFED590CB3AA7CB7C5F74911D8912C29D6233F4D53BC64139E2F55BE75507DD77868E384AEC581F3F411DB1A742972D3EBFD3315C84A5AD63A0E75C8BCA3E3041E05D9067AFF3B1244F763E7983";
    let encapsulation_key = (0..test_encapsulation_key.len())
        .step_by(2)
        .map(|i| {
            test_encapsulation_key
                .get(i..i + 2)
                .and_then(|sub| u8::from_str_radix(sub, 16).ok())
                .unwrap()
        })
        .collect();

    let mut lockboxes = vec![];
    lockboxes.push(Lockbox::new(
        lockbox_algorithm,
        &encapsulation_key,
        &symmetric_key,
    )?);

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

    let tap = AttestationPayload { digests, secrets };

    let serializer = AttestationPayloadSerializer::new();
    let serialized = serializer.serialize(lockboxes, tap)?;

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
