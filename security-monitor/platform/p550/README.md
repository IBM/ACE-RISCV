# Supported hardware

## SiFive P550 evaluation board
This RISC-V processor is not compliant with RISC-V CoVE spec because it does not implement the Sstc extension. We have a version of ACE that implements missing features and thus runs on P550.

Build first the clean version of SiFive firmware. We use the version `2024.09.00-HFP550` because this is the version that was available when we were working with P550.
```
export YOCTO_DIR=/tmp/yocto
mkdir -p $YOCTO_DIR && cd $YOCTO_DIR
git clone https://github.com/sifive/freedom-u-sdk.git -b 2024.09.00-HFP550
BB_NUMBER_THREADS="192" PARALLEL_MAKE="-j 192" kas build $YOCTO_DIR/freedom-u-sdk/scripts/kas/hifive-premier-p550.yml
```

At this point, we have built the original SiFive P550 firmware. Let's build now the ACE security monitor. Make sure that we have access to the same compiler that yocto used to compile OpenSBI firmware.
```
export RISCV_GNU_TOOLCHAIN_WORK_DIR=$YOCTO_DIR/build/tmp/sysroots-components/x86_64/gcc-cross-riscv64/usr/bin/riscv64-freedomusdk-linux/
ls -lah $RISCV_GNU_TOOLCHAIN_WORK_DIR/riscv64-freedomusdk-linux-gcc
```

Let's download ACE sources and build the ACE security monitor for P550.
```
ACE_SRC=/tmp/ace
git clone --recurse-submodules -b sifive_p550 git@github.com:IBM/ACE-RISCV.git $ACE_SRC
cd $ACE_SRC
make -j192 security_monitor
```

Let's patch SiFive's firmware so that we build its version linked with the ACE security monitor.
```
cd meta-sifive
git apply $ACE_SRC/security-monitor/platform/p550/patches/meta-sifive/ace.patch
cd ../
cd openembedded-core
git apply /home/woz/ace/security-monitor/platform/p550/patches/openembedded-core/qemu_ace.patch
cd ../
```

Now its time to build the patched firmware again. Yocto will rebuilt only the components we patched, so the build process will be much faster than the initial build.
```
BB_NUMBER_THREADS="192" PARALLEL_MAKE="-j 192" kas build $YOCTO_DIR/freedom-u-sdk/scripts/kas/hifive-premier-p550.yml
```

Now you can flash the new version of firmware following the standard procedure described by SiFive on its website.
```
# Firmware including the ACE security monitor
ls $YOCTO_DIR/build/tmp/deploy/images/hifive-premier-p550/bootloader_ddr5_secboot.bin
```

I did not have time to prepare nice Linux kernel patches for yocto, so you should build the Linux kernel with CoVE patches from sources `https://github.com/wojciechozga/linux-cove/tree/woz/linux_6.6.21_ace_p550` or using buildroot:
```
cd $ACE_SRC
make -j192 hypervisor
# the Linux kernel Image should be here
ls $ACE_DIR/build/hypervisor/buildroot/build/linux-6.6.21/arch/riscv/boot/Image.gz
```

After all, you can copy `Image.gz` to P550 with `scp` and then copy it to the /boot folder and reboot the system. If everything went well, you should see that KVM printed the following line to dmesg
```
hifive-premier-p550:~$ dmesg | grep TSM
[    1.126289] kvm [1]: TSM version 9 is loaded and ready to run
```

Now, you can run a confidential VM
```
KERNEL=/path_to_TVM_kernel
DRIVE=/path_to_TVM_filesystem
TAP=/path_to_TVM_TAP
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