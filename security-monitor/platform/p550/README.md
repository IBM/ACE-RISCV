# Supported hardware

## SiFive P550 evaluation board
This RISC-V processor is not compliant with the RISC-V CoVE specification because (1) it implements a pre-ratified version of the H extension, and (2) it does not support the Sstc extension. However, we have developed a version of ACE that emulates these missing hardware features. As a result, we are able to experimentally run ACE on the SiFive P550.

Below process is not well integrated with YOCTO and requires manual execution of certain steps. We welcome pull requests to provide YOCTO integration.

### Build SiFive p550 firmware
We begin by building the SiFive firmware without any modifications. We use version `2024.09.00-HFP550`, as it was the version available at the time we worked with the P550 evaluation board.

```
export YOCTO_DIR=/tmp/yocto
mkdir -p $YOCTO_DIR && cd $YOCTO_DIR
git clone https://github.com/sifive/freedom-u-sdk.git -b 2024.09.00-HFP550
BB_NUMBER_THREADS="192" PARALLEL_MAKE="-j 192" kas build $YOCTO_DIR/freedom-u-sdk/scripts/kas/hifive-premier-p550.yml
```

At this point, we have built the original SiFive P550 firmware. We will need the same compiler that built SiFive firmware to build ACE components.

### Build ACE security monitor
Let's build now the ACE security monitor. Make sure that we have access to the same compiler that yocto used to compile OpenSBI firmware.
```
YOCTO_RISCV_GNU_TOOLCHAIN_DIR=$YOCTO_DIR/build/tmp/sysroots-components/x86_64/gcc-cross-riscv64/usr/bin/riscv64-freedomusdk-linux/
YOCTO_CROSS_COMPILE=riscv64-freedomusdk-linux-
ls -lah $YOCTO_RISCV_GNU_TOOLCHAIN_DIR/${YOCTO_CROSS_COMPILE}gcc
```

Let's download ACE sources dedicated for SiFive P550.
```
export ACE_SRC=/tmp/ace
export ACE_DIR=$ACE_SRC/build/
git clone --recurse-submodules -b sifive_p550 git@github.com:IBM/ACE-RISCV.git $ACE_SRC
```

Build the version of the ACE security monitor dedicated for P550.
```
RISCV_GNU_TOOLCHAIN_WORK_DIR=$YOCTO_RISCV_GNU_TOOLCHAIN_DIR CROSS_COMPILE=$YOCTO_CROSS_COMPILE make -j192 -C $ACE_SRC security_monitor
```

Check presentence of the static library (`libace.a`) that contains the ACE security monitor.
```
ls -lah $ACE_DIR/security-monitor/libace.a
```

### Build OpenSBI linked with the ACE security monitor
Let's patch SiFive's firmware. We will build OpenSBI version that is linked with the ACE security monitor and QEMU patches with support to run confidential VMs.
```
cd $YOCTO_DIR/meta-sifive
git apply $ACE_SRC/security-monitor/platform/p550/patches/meta-sifive/ace.patch
cd $YOCTO_DIR/openembedded-core
git apply /home/woz/ace/security-monitor/platform/p550/patches/openembedded-core/qemu_ace.patch
```

Now its time to build the patched firmware again. Yocto will rebuilt only the components we patched, so the build process will be much faster than the initial build.
```
BB_NUMBER_THREADS="192" PARALLEL_MAKE="-j 192" kas build $YOCTO_DIR/freedom-u-sdk/scripts/kas/hifive-premier-p550.yml
```

Check that the firmware has been built.
```
ls -lah $YOCTO_DIR/build/tmp/deploy/images/hifive-premier-p550/bootloader_ddr5_secboot.bin
```

Now you can flash the new version of firmware following the standard procedure described by SiFive on its website.

### Build host Linux kernel
```
cd $ACE_SRC
RISCV_GNU_TOOLCHAIN_WORK_DIR=$YOCTO_RISCV_GNU_TOOLCHAIN_DIR CROSS_COMPILE=$YOCTO_CROSS_COMPILE make -j192 hypervisor
```

Check that the host Linux kernel image was built:
```
ls -lah $ACE_DIR/hypervisor/buildroot/build/linux-6.6.21/arch/riscv/boot/Image.gz
```

You can copy `Image.gz` to P550 with `scp` and then copy it to the /boot folder and reboot the system.
```
scp $ACE_DIR/hypervisor/buildroot/build/linux-6.6.21/arch/riscv/boot/Image.gz login@ip_of_p550:/tmp
# you must adjust below command so that you copy to the location of the boot drive:
sudo cp /tmp/Image.gz /run/media/boot-mmcblk0p1/Image.gz
```

Once you start your evaluation board with firmware containing ACE and host Linux kernel contianing CoVE patches, you should see that KVM printed the following line to dmesg:
```
dmesg | grep TSM
# expected output:
# [    1.126289] kvm [1]: TSM version 9 is loaded and ready to run
```

### Build a test confidential VM
```
cd $ACE_SRC
make -j192 confidential_vms
```

Check that the VM image was built:
```
ls -lah $ACE_DIR/confidential_vms/linux_vm/buildroot/images/*
# The following files should be present
#   Image - contains guest Linux kernel
#   rootfs.ext4 - root filesystem
#   cove_tap_qemu - TVM attestation payload (for local attestation)
```

Now, use the `scp` tool to copy the VM image files to your P550 evaluation board.
```
scp $ACE_DIR/confidential_vms/linux_vm/buildroot/images/* login@ip_of_p550:/tmp
```

Now, run the test confidential VM on P550:
```
KERNEL=/tmp/Image
DRIVE=/tmp/rootfs.ext4
TAP=/tmp/cove_tap_qemu
SMP=1
MEMORY=1G
HOST_PORT=10101

qemu-system-riscv64 --enable-kvm -nographic \
    -machine virt,cove=true,cove-tap-filename=${TAP} -cpu rv64,sstc=false,f=true -smp ${SMP} -m ${MEMORY} \
    -kernel ${KERNEL} \
    -global virtio-mmio.force-legacy=false \
    -append "ro root=/dev/vda swiotlb=mmnn,force" \
    -device virtio-blk-pci,drive=hd0,iommu_platform=on,disable-legacy=on,disable-modern=off \
    -drive if=none,format=raw,file=${DRIVE},id=hd0 \
    -device virtio-net-pci,netdev=net0,iommu_platform=on,disable-legacy=on,disable-modern=off \
    -netdev user,id=net0,net=192.168.100.1/24,dhcpstart=192.168.100.128,hostfwd=tcp::${HOST_PORT}-:22
```

After a few seconds, you should see the login prompt to your confidential VM. Congratulations!
```
# credentials to test confidential VM
login: root
password: passwd
```