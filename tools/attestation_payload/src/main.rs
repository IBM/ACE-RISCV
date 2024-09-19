// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use clap::{Parser, Subcommand};
use crate::error::Error;

mod error;
mod constants;
mod generate;
mod append;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    cmd: Commands
}

#[derive(Subcommand, Debug, Clone)]
enum Commands {
    Append {
        #[arg(short, long)]
        input_file: String,
        #[arg(short, long)]
        tap_file: String,
        #[arg(short, long)]
        output_file: Option<String>,
    },
    Generate {
        #[arg(short='k', long)]
        kernel_file: String,
        #[arg(short='b', long)]
        kernel_commandline: String,
        #[arg(short, long)]
        initramfs_file: String,
        #[arg(value_parser = parse_key_val::<usize, String>)]
        confidential_vm_secrets: Vec<(usize, String)>,
        #[clap(short, long, value_delimiter = ' ', num_args = 1..)]
        tee_public_keys_files: Vec<String>,
        #[arg(short, long)]
        output_file: String,
    }
}

/// Parse a single key-value pair
fn parse_key_val<T, U>(s: &str) -> Result<(T, U), Box<dyn std::error::Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: std::error::Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: std::error::Error + Send + Sync + 'static,
{
    let pos = s
        .find('=')
        .ok_or_else(|| format!("invalid KEY=value: no `=` found in `{s}`"))?;
    Ok((s[..pos].parse()?, s[pos + 1..].parse()?))
}

fn main() -> Result<(), Error> {
    Ok(match Args::parse().cmd {
        Commands::Append {input_file, tap_file, output_file} => append::append_tap(input_file, tap_file, output_file),
        Commands::Generate {kernel_file, kernel_commandline, initramfs_file, confidential_vm_secrets, tee_public_keys_files, output_file} => generate::generate_tap(kernel_file, kernel_commandline, initramfs_file, confidential_vm_secrets, tee_public_keys_files, output_file),
    }?)
}

