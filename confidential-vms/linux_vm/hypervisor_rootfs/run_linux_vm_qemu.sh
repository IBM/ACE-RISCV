#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

HOST_PORT="$((3000 + RANDOM % 3000))"
INTERACTIVE="-nographic"
SMP=2
MEMORY=1G
ID=""

for i in "$@"; do
  case $i in
    -e=*|--debug-port=*)
      DEBUG_PORT="${i#*=}"
      DEBUG_OPTIONS="-gdb tcp::${DEBUG_PORT} -S -d in_asm -D debug.log"
      echo ${DEBUG_OPTIONS}
      shift
      ;;
    --host-port=*)
      HOST_PORT="${i#*=}"
      shift
      ;;
    -s=*|--smp=*)
      SMP="${i#*=}"
      shift
      ;;
    -m=*|--memory=*)
      MEMORY="${i#*=}"
      shift
      ;;
    -i=*|--id=*)
      ID="${i#*=}"
      shift
      ;;
    --daemonize*)
      INTERACTIVE="-daemonize"
      shift
      ;;
    -*|--*)
      echo "Unknown option $i"
      exit 1
      ;;
    *)
      ;;
  esac
done

if [ ! -f "/root/linux_vm${ID}" ]; then
  cp -rf /root/linux_vm /root/linux_vm${ID}
fi

QEMU_CMD=qemu-system-riscv64
KERNEL=/root/linux_vm${ID}/Image
DRIVE=/root/linux_vm${ID}/rootfs.ext2
INITRAMFS=/root/linux_vm${ID}/rootfs.cpio
TAP=/root/linux_vm${ID}/cove_tap_qemu

echo "SSH port: ${HOST_PORT}"
echo "Number of cores assigned to the guest: ${SMP}"
echo "${INTERACTIVE}"

${QEMU_CMD} ${DEBUG_OPTIONS} \
    ${INTERACTIVE} \
    --enable-kvm \
    -machine virt,cove=true,cove-tap-filename=${TAP} -cpu rv64,f=true -smp ${SMP} -m ${MEMORY} \
    -kernel ${KERNEL} \
    -seed 0 \
    -global virtio-mmio.force-legacy=false \
    -append "console=ttyS0 ro root=/dev/vda swiotlb=mmnn,force" \
    -device virtio-blk-pci,drive=hd0,iommu_platform=on,disable-legacy=on,disable-modern=off \
    -drive if=none,format=raw,file=${DRIVE},id=hd0 \
    -device virtio-net-pci,netdev=net0,iommu_platform=on,disable-legacy=on,disable-modern=off \
    -netdev user,id=net0,net=192.168.100.1/24,dhcpstart=192.168.100.128,hostfwd=tcp::${HOST_PORT}-:22
