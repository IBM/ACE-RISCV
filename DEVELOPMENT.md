# Development Guide

## Setup of a shared development machine
We use `/opt` as a shared directory to which we install common tools, like Rust.

### Install a shared version of Rust
```
mkdir /opt/rust
curl https://sh.rustup.rs -sSf | sudo env RUSTUP_HOME=/opt/rust/rustup CARGO_HOME=/opt/rust/cargo sh -s -- --default-toolchain stable --profile default --no-modify-path -y
sudo env PATH=${PATH} RUSTUP_HOME=/opt/rust/rustup CARGO_HOME=/opt/rust/cargo rustup default nightly
sudo env PATH=${PATH} RUSTUP_HOME=/opt/rust/rustup CARGO_HOME=/opt/rust/cargo rustup target add riscv64gc-unknown-none-elf
source "/opt/rust/cargo/env"
cargo install cargo-binutils
```

Every user on the system needs to create his own cargo directory:
```
mkdir ~/.cargo
cp /opt/rust/cargo/env ~/.cargo/
```

Every user must configure his `~/.bashrc` script to setup correct paths to the global installation of Rust:
```
vim ~/.bashrc
# check that the below lines are in the ~/.bashrc

. "$HOME/.cargo/env"
export RUSTUP_HOME=/opt/rust/rustup
export PATH=${PATH}:/opt/rust/cargo/bin
```

### Build directory
By default, ACE will be installed in the `build/` directory of this repository. You can install it to an alternative location by specifying the `ACE_DIR` environment variable. Please make sure that you have enough permissions to install in that location.
```
export ACE_DIR="/opt/ace/"
```

## Modify the hypervisor
Files in `configurations/overlay/root` will be included in the hypervisor filesystem during the build process. 

To re-build the hypervisor without building all other components run:
```
make rootfs
```

You can modify the kernel driver (`configurations/overlay/root/ace-kernel-module`) using the following command:
```
make overlay rootfs
```

## Run & Test
To start the hypervisor inside the RISC-V emulator and automatically connect to it over SSH run the following command:
```
${ACE_DIR}/tools/ace start
```

To stop, exit the guest's shell started with the command above. Alternatively, run the following command from other terminal:
```
${ACE_DIR}/tools/ace stop
```

Run integration tests:
```
${ACE_DIR}/tools/ace test
```

## Debug
You need two ssh terminals. In the first one, you run the emulator (qemu) while in the second one you run the debugger (gdb).

First console:
```
${ACE_DIR}/tools/ace start --debug-port=1234
```

Second console:
```
riscv64-unknown-linux-gnu-gdb

# connect to the QEMU from the gdb console
(gdb) target remote localhost:1234
# set up some breakpoint on addresses you want to debug
(gdb) breakpoint *0x1000
# instruct the emulator to start executing the very first boot instruction
(gdb) continue
...
```

Alternative:
```
riscv64-unknown-linux-gnu-gdb -ex 'target remote localhost:1234'

(gdb) file /opt/ace/opensbi/platform/generic/firmware/fw_payload.elf
(gdb) continue
(gdb) disassemble main
(gdb) b *main+20
(gdb) b *sm_to_svm_asm
(gdb) b *sm_trap_vector_asm
(gdb) continue
(gdb) si
(gdb) i r a0
...
```

Disassembly the firmware payload to learn about addresses and instructions:
```
${ACE_DIR}/riscv-gnu-toolchain/bin/riscv64-unknown-linux-gnu-objdump -D ${ACE_DIR}/opensbi/platform/generic/firmware/fw_payload.elf
```

## Commiting changes
Always sign commits. Use the following commands to configure your git to use SSH keys for signing.
```
git config --global user.name "Name Surname"
git config --global user.email "name@surname.com"
git config --global gpg.format ssh
git config --global user.signingkey ~/.ssh/id_rsa.pub
git config --global commit.gpgsign true

eval "$(ssh-agent -s)"
ssh-add  ~/.ssh/id_rsa
```

## Troubleshooting
**Disconnected during the build process**
Make sure you set up keep alive configuration to your ssh connection.
```
vim ~/.ssh/config

# set this:
Host hostname.of.development.server
    TcpKeepAlive Yes
    ServerAliveInterval 30
```

**Too little disk space assigned to your system**
Expand current partition space to unallocated disk. 

Check the name of the disk
```
sudo fdisk -l
```

Create new primary partition, set type as linux lvm.
```
sudo fdisk /dev/nvme0n1

(fdisk) n
(fdisk) p
(fdisk) 3
(fdisk) t
(fdisk) 8e
(fdisk) w
```
Create a new primary volume and extend the volume group to the new volume.
```
sudo partprobe
sudo pvcreate /dev/nvme0n1p3
sudo vgextend fedora_fedora /dev/nvme0n1p3
```

Check the physical volume for free space, extend the logical volume with the free space.
```
sudo vgdisplay -v
sudo lvextend -l +100%FREE /dev/mapper/fedora_fedora-root
```

Finally perform an online resize to resize the logical volume, then check the available space.
```
# xfs_growfs or resize2fs!
sudo xfs_growfs /dev/mapper/fedora_fedora-root
df -h
```