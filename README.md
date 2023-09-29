# Assured Confidential Execution (ACE) for RISC-V  
ACE-RISCV is an open-source project, which goal is to deliver a confidential computing framework with a formally proven firmware. It is based on the [canonical architecture](https://arxiv.org/abs/2308.10249) and targets RISC-V with the goal of being able to be ported to other architectures. Formal verification efforts focus on the [security monitor](security-monitor/) implementation. We invite collaborators to work together to push the boundaries of confidential computing technology. 

**It is an active research project, without warranties of any kind.**

## Quick Start
Follow instructions to run a sample [confidential workload](harness/baremetal) under an [untrusted Linux-based hypervisor](hypervisor/) in an [emulated RISC-V environment](qemu/). 

### Requirements
The full compilation of the framework takes long time because we build all tools from sources. These are: the RISC-V compiler (`riscv-toolchain`), RISC-V emulator (`qemu`), hypervisor kernel (`Linux kernel`), and firmware (`security monitor` with `OpenSBI firmware`). Make sure to build this project on a machine with at least 4 cores, 4GB RAM, and 50GB disk space for reasonable (~30min) build time.

### Dependencies
<details>
<summary>Dependencies for Fedora 36 (click to see)</summary>

```
# riscv-gnu-toolchain dependencies:
sudo yum install -y autoconf automake python3 libmpc-devel mpfr-devel gmp-devel gawk  bison flex texinfo patchutils gcc gcc-c++ zlib-devel expat-devel

# Qemu
sudo dnf groupinstall -y "Development Tools"
sudo dnf install -y automake gcc make glibc ninja-build glib2-devel pixman-devel

# Buildroot
sudo dnf groupinstall -y "Development Tools" "Development Libraries"
sudo dnf install -y which sed make binutils diffutils gcc g++ bash patch gzip bzip2 perl tar cpio unzip rsync file bc findutils
```

</details>

<details>
<summary>Dependencies for Ubuntu 22.04 (click to see)</summary>

```
sudo apt update

# riscv-gnu-toolchain dependencies:
sudo apt -qq -y install autoconf automake autotools-dev curl python3 libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev

# OpenSBI
sudo apt -qq -y install clang

# Qemu
sudo apt -qq -y install git libglib2.0-dev libfdt-dev libpixman-1-dev zlib1g-dev ninja-build 

# Buildroot
sudo apt -qq -y install unzip sed binutils diffutils build-essential bash patch gzip bzip2 perl tar cpio unzip rsync file bc findutils

# utilities
sudo apt install -y sshpass
```

</details>

Install the latest Rust:
```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source "$HOME/.cargo/env"
rustup default nightly
rustup target add riscv64gc-unknown-none-elf
rustup component add rustfmt
cargo install cargo-binutils

# make sure that the below line is in the ~/.bashrc
. "$HOME/.cargo/env"
```

### Sources & Patches
Checkout this repository with submodules (takes long time!):
```
git clone --recurse-submodules git@github.com:IBM/ACE-RISCV.git
```

### Compilation
Run the following commands from the directory where this README file is.

#### Prerequisites
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
You can build individual components to avoid long builds that can lead to 'ssh disconnections', 'hangups', and similar.

Install all develoment tools required to compile code for risc-v architecture:
```
make devtools
```

Build the host and guest Linux-based OSes
```
make hypervisor
```

Build the firmware that will boot the system and the security monitor (SM)
```
make firmware
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

Run the hypervisor with ACE on a RISC-V emulator:
```
${ACE_DIR}/tools/ace run
```

You should see the output from the boot process and a login promt:
```
# login: root, password: passwd
```

Run a sample confidential VM:
```
./run.sh
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