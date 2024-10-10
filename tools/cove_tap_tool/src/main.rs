// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use clap::{Parser, Subcommand};

mod attach;
mod error;
mod generate;
mod measure;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    cmd: Commands,
}

#[derive(Subcommand, Debug, Clone)]
enum Commands {
    Attach {
        #[arg(short, long)]
        input_file: String,
        #[arg(short, long)]
        tap_file: String,
        #[arg(short, long)]
        output_file: Option<String>,
    },
    Generate {
        #[arg(short='p', long="pcrs", value_parser = parse_key_val::<u16, String>, value_delimiter = ',', required=true)]
        pcrs: Vec<(u16, Vec<u8>)>,
        #[arg(long="secrets", value_parser = parse_key_val::<u64, String>, value_delimiter = ',')]
        confidential_vm_secrets: Vec<(u64, Vec<u8>)>,
        #[clap(short, long, value_delimiter = ' ', num_args = 1..)]
        tee_public_keys_files: Vec<String>,
        #[arg(short, long)]
        output_file: String,
    },
    Measure {
        #[arg(short, long)]
        kernel_file: String,
    },
}

/// Parse a single key-value pair
fn parse_key_val<T, U>(
    s: &str,
) -> Result<(T, Vec<u8>), Box<dyn std::error::Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: std::error::Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: std::error::Error + Send + Sync + 'static,
{
    let pos = s
        .find('=')
        .ok_or_else(|| format!("invalid KEY=value: no `=` found in `{s}`"))?;
    let key = s[..pos].parse()?;
    let value = &s[pos + 1..];
    let value = if value.starts_with("0x") {
        decode_hex(&value[2..])?
    } else {
        value.as_bytes().to_vec()
    };
    Ok((key, value))
}

pub fn decode_hex(s: &str) -> Result<Vec<u8>, core::num::ParseIntError> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect()
}

fn main() -> Result<(), Error> {
    Ok(match Args::parse().cmd {
        Commands::Attach {
            input_file,
            tap_file,
            output_file,
        } => attach::attach_tap(input_file, tap_file, output_file),
        Commands::Generate {
            pcrs,
            confidential_vm_secrets,
            tee_public_keys_files,
            output_file,
        } => generate::generate_tap(
            pcrs,
            confidential_vm_secrets,
            tee_public_keys_files,
            output_file,
        ),
        Commands::Measure { kernel_file } => measure::measure(kernel_file),
    }?)
}
