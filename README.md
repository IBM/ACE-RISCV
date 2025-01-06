# Assured Confidential Execution (ACE) for RISC-V
![Build Status](https://github.com/IBM/ACE-RISCV/actions/workflows/build.yml/badge.svg?branch=main)

<img src=".github/ace.png" align="right" width="100" height="100">

ACE-RISCV is an open-source project, whose goal is to deliver a confidential computing framework with a formally proven security monitor. It is based on the [canonical architecture](https://dl.acm.org/doi/pdf/10.1145/3623652.3623668) and targets RISC-V with the goal of being portable to other architectures. The formal verification efforts focus on the [security monitor implementation](security-monitor/). We invite collaborators to work with us to push the boundaries of provable confidential computing technology.

This project implements the RISC-V CoVE spec's deployment model 3 referenced in [Appendix D](https://github.com/riscv-non-isa/riscv-ap-tee/blob/main/). The formal specification is embedded in the security monitor's source code and the proofs are in the [verification/](verification/) folder. Please read our [paper](https://dl.acm.org/doi/pdf/10.1145/3623652.3623668) to learn about the approach and goals.

## Hardware requirements
We are currently building on RISC-V 64-bit with integer (I), atomic (A) and hypervisor extentions (H), physical memory protection (PMP), memory management unit (MMU), IOPMP, core-local interrupt controller (CLINT), and supervisor timecmp extension (Sstc).

## Quick Start
Follow instructions to run one of the sample [confidential workloads](confidential-vms) under an [untrusted Linux KVM hypervisor](hypervisor/) in an emulated RISC-V environment.

### Requirements
Full compilation of the framework takes a long time because many tools are built from sources. Our toolchain currently includes: hypervisor kernel (`Linux kernel`), confidential guest kernel (`Linux kernel`) and firmware (`security monitor` with `OpenSBI firmware`). Make sure to build this project on a machine with at least 4 cores, 4GB RAM, and 50GB disk space for reasonable (~30min) build time.

### Dependencies
You must install build dependencies specific to the operating system you use AND install the Rust toolchain. You can also look at the [reproducible build configuration](.github/workflows/build.yml) of the continous integration (CI) system.

Dependencies for Ubuntu 22.04
```
sudo apt update

# riscv-gnu-toolchain dependencies:
sudo apt -qq -y install autoconf automake autotools-dev curl python3 libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev xz-utils

# OpenSBI
sudo apt -qq -y install clang

# Qemu 8.2
sudo apt -qq -y install git libglib2.0-dev libfdt-dev libpixman-1-dev zlib1g-dev ninja-build python3-venv libslirp-dev

# Buildroot
sudo apt -qq -y install unzip sed binutils diffutils build-essential bash patch gzip bzip2 perl tar cpio unzip rsync file bc findutils

# utilities
sudo apt install -y sshpass
```

Install the latest Rust:
```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source "$HOME/.cargo/env"
rustup default nightly
rustup target add riscv64gc-unknown-none-elf
rustup component add rustfmt
cargo install cargo-binutils

# check that the below lines are in the ~/.bashrc
. "$HOME/.cargo/env"
```

### Sources
Checkout this repository with submodules:
```
git clone --recurse-submodules git@github.com:IBM/ACE-RISCV.git
```

### Compilation
#### Prerequisites
Run the following commands from the directory containing this README file.

Make sure once again that all submodules are fetched:
```
git submodule update --init --recursive
```

Set up the ACE_DIR variable to point to the location where the project will build. Default is the `build/` subdirectory of the location where you will execute the `make` command.
```
export ACE_DIR=/your/path/to/build/ace
```

#### Build everything
The following command will build the entire framework. Set `-j` flag to the number of processor cores you have in the system. Below command assumes that you have 4 cores.
```
MAKEFLAGS="--silent -j4" make
```

#### Build individual components
Alternativly, you can build individual components to avoid long builds that can lead to 'ssh disconnections', 'hangups', and similar issues.

Install all develoment tools required to compile code for the RISC-V architecture:
```
make devtools
```

Build the host OS -- [a Linux KVM hypervisor](hypervisor/):
```
make hypervisor
```

Build [the low level firmware](security-monitor/opensbi) responsible for the boot process. This command will also build the [security monitor (SM)](security-monitor/):
```
make firmware
```

Build sample [confidential workloads](confidential-vms/):
```
make confidential_vms
```

Build the RISC-V emulator and utility tools that simplify running the test environment:
```
make emulator
```

## Run and Test
Make sure you have the `ACE_DIR` environmental variable set and it points to the location of your build. Check the 'Compilation' section in case this variable is not set.
```
echo $ACE_DIR
```

To run the test environment on a RISC-V emulator run:
```
${ACE_DIR}/tools/ace run
```

You should see the output from the boot process and a promt to login to the hypervisor:
```
# login: root, password: passwd
```

To run the sample Linux OS as a confidential VM (login: root, password: passwd) execute.
This demonstrates automatic promotion of a VM to TVM:
```
./run_linux_vm_qemu.sh
```

Run the sample Linux OS as a confidential VM using kvmtool.
```
./run_linux_vm_kvmtool.sh
```

## Local attestation
Local attestation allows you to expose secrets (e.g., dm-crypt/LUKS key, TLS pre-shared key, etc) to your confidential VM in a secure way.

Collect reference measurements of your virtual machines, like kernel, initrd, initial boot hart state.
Below as, an example, we just collect the kernel measurement (for automatic promotion):
```
cove-tap-tool measure --kernel-file $ACE_DIR/confidential_vms/linux_vm/buildroot/images/Image
# Example output:
# Digest 0x86774eec200ca6552cbc50211e4b32e7a4ba815c190d56b11ffabc8df1ebb6d9c41d04a64099d860b90c65729a28ded8
```

Create a TVM attestation payload (TAP) that contains a secret (0xc0ffee), which will be release to confidential VMs whose measurement in PCR4 equals the reference measurement of your kernel.
Please note that in real systems you would define values of more PCRs to ensure the integrity of the firmware, security monitor, initrd, etc.
```
cove-tap-tool generate --output-file=$ACE_DIR/cove_tap --pcrs 4=0x86774eec200ca6552cbc50211e4b32e7a4ba815c190d56b11ffabc8df1ebb6d9c41d04a64099d860b90c65729a28ded8 --secrets 0=0xc0ffee
# Example output:
# Writing PCR4=86774eec200ca6552cbc50211e4b32e7a4ba815c190d56b11ffabc8df1ebb6d9c41d04a64099d860b90c65729a28ded8
# Writing secret 0
```

Attach the TAP to the kernel image:
```
cove-tap-tool append --tap-file=$ACE_DIR/cove_tap --kernel-file=$ACE_DIR/confidential_vms/linux_vm/buildroot/images/Image
```

Run again the hypervisor and then your confidential VM (see section `Run and Test`).
You should see the output
```
#ACE: Reference PCR4=Sha512=0x86774eec200ca6552cbc50211e4b32e7a4ba815c190d56b11ffabc8df1ebb6d9c41d04a64099d860b90c65729a28ded8
#ACE: Attestation succeeded, read 1 secret
```

You can read the secret from the inside of the confidential VM:
```
# if the root file system has not been mounted, then execute below:
mount /dev/vda /root
cd /root/root/ace_module
insmod ace.ko
```

You should see the secret:
```
[  203.051959] Requesting secret from the security monitor
[  203.107150] Secret=0xc0ffee
```

Integrating local attestation with dm-crypt/LUKS is work in progress. When finished, you will be able to encrypt your rootfs and pass the decryption key via TAP.
A script in initrd will then retrieve the decryption key from TAP and decrypt the rootfs.

# License
This repository is distributed under the terms of the Apache 2.0 License, see [LICENSE](LICENSE).

**This is an active research project, without warranties of any kind.**

# Citation
```
@inproceedings{ozga2023riscvtee,
    title={Towards a Formally Verified Security Monitor for VM-based Confidential Computing},
    author={Ozga, Wojciech and Hunt, Guerney D. H. and Le, Michael V. and Palmer, Elaine R. and Shinnar, Avraham},
    booktitle = {Proceedings of the 12th International Workshop on Hardware and Architectural Support for Security and Privacy},
    series = {HASP2023},
    year={2023}
}
```
