# Assured Confidential Execution (ACE) for RISC-V
![Build Status](https://github.com/IBM/ACE-RISCV/actions/workflows/build.yml/badge.svg?branch=main)

<img src=".github/ace.png" align="right" width="100" height="100">

ACE-RISCV is an open-source project, whose goal is to deliver a confidential computing framework with a formally proven security monitor. It is based on the [canonical architecture](https://dl.acm.org/doi/pdf/10.1145/3623652.3623668) and targets RISC-V with the goal of being portable to other architectures. The formal verification efforts focus on the [security monitor](security-monitor/) implementation. We invite collaborators to work with us to push the boundaries of provable confidential computing technology.

**This is an active research project, without warranties of any kind.** Please read our [paper](https://dl.acm.org/doi/pdf/10.1145/3623652.3623668) to learn about our approach and goals.

## Hardware requirements
We are currently building on RISC-V with hypervisor extentions, physical memory protection (PMP), IOPMP, and supervisor timecmp extension (Sstc). We plan to adapt some of the RISC-V confidential computing extensions, such as [the CoVE extension](https://github.com/riscv-non-isa/riscv-ap-tee/blob/main/specification/riscv-cove.pdf) and [the Smmtt extension](https://github.com/riscv/riscv-smmtt).

## Quick Start
Follow instructions to run a sample [confidential workload](harness/baremetal) under an [untrusted Linux-based hypervisor](hypervisor/) in an [emulated RISC-V environment](qemu/).

### Requirements
Full compilation of the framework takes a long time because all the tools are built from sources. Our tool chain currently includes: RISC-V emulator (`qemu`), hypervisor kernel (`Linux kernel`), and firmware (`security monitor` with `OpenSBI firmware`). Make sure to build this project on a machine with at least 4 cores, 4GB RAM, and 50GB disk space for reasonable (~30min) build time.

### Dependencies
You must install build dependencies specific to the operating system you use AND install the Rust toolchain.

Dependencies for Ubuntu 22.04
```
sudo apt update

# riscv-gnu-toolchain dependencies:
sudo apt -qq -y install autoconf automake autotools-dev curl python3 libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev

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

### Sources & Patches
Checkout this repository with submodules (this takes a long time!):
```
git clone --recurse-submodules git@github.com:IBM/ACE-RISCV.git
```

### Compilation
#### Prerequisites
Run the following commands from the directory containing this README file.

Set up the ACE_DIR variable to point to the location where the project will build. Default is the build/ subdirectory of the location where you will execute `make` command.
```
export ACE_DIR=/your/path/to/build/ace
```

#### Build everything
The following command will build the entire framework. Set `-j` flag to the number of processor cores you have in the system.
```
MAKEFLAGS="--silent -j4" make
```

#### Build individual components
Alternativly, you can build individual components to avoid long builds that can lead to 'ssh disconnections', 'hangups', and similar issues.

Install all develoment tools required to compile code for risc-v architecture:
```
make devtools
```

Build the host and guest Linux-based OSes
```
make hypervisor
```

Build the security monitor (SM)
```
make security_monitor
```

Build the firmware that will boot the system
```
make firmware
```

Build test confidential VMs
```
make confidential_vms
```

Build the RISC-V emulator and tools that will simplify running the test environment
```
make emulator
```

## Run and Test
Make sure you have the ACE_DIR environmental variable set and it points to the location of your build. Check 'compilation' section in case this variable is not set.
```
echo $ACE_DIR
```

To run the test environment on a RISC-V emulator run:
```
${ACE_DIR}/tools/ace run
```

You should see the output from the boot process and a promt to login to the hypervisor.
```
# login: root, password: passwd
```

To run the sample `baremetal` confidential VM execute:
```
./run_baremetal.sh
```

To run the sample Linux kernel confidential VM execute:
```
./run_linux_vm.sh
```

## Build on MacOS
While MacOS is not fully supported by us, building the security monitor on MacOS is also possible.
We have not tested building the hypervisor on MacOS or running the VMs in Qemu.

1. Install basic dependencies.
```
brew install coreutils  # to have nproc available
brew install autoconf automake curl python libmpc mpfr gmp gawk flex texinfo libtool bc expat # for OpenSBI build
```

2. Install the Risc-V toolchain.
```
# https://github.com/riscv-software-src/homebrew-riscv
brew tap riscv-software-src/riscv
brew install riscv-gnu-toolchain
```

3. Source environment variables for using the toolchain.
```
source macos_env
```

4. Build the security monitor:
```
make security_monitor
```

# License
This repository is distributed under the terms of the Apache 2.0 License, see [LICENSE](LICENSE).

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
