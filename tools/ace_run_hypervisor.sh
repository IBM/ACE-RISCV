#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

if [ -z ${ACE_DIR} ]; then
    echo "ACE_DIR must point to the directory where ACE is installed"
    exit 1
fi

QEMU_CMD=${ACE_DIR}/qemu/bin/qemu-system-riscv64
KERNEL=${ACE_DIR}/security-monitor/opensbi/platform/generic/firmware/fw_payload.elf
DRIVE=${ACE_DIR}/hypervisor/buildroot/images/rootfs.ext4

HOST_PORT="$((3000 + RANDOM % 3000))"
INTERACTIVE="-nographic"
SMP=4
MEMORY=8G

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

echo "SSH port: ${HOST_PORT}"
echo "Number of cores assigned to the guest: ${SMP}"

${QEMU_CMD} ${DEBUG_OPTIONS} \
    -m ${MEMORY} \
    ${INTERACTIVE} \
    -machine virt -cpu rv64 \
    -bios none \
    -kernel ${KERNEL} \
    -global virtio-mmio.force-legacy=false \
    -append "console=ttyS0 ro root=/dev/vda" \
    -drive if=none,format=raw,file=${DRIVE},id=hd0 \
    -device virtio-blk-device,scsi=off,drive=hd0 \
    -netdev user,id=net0,net=192.168.100.1/24,dhcpstart=192.168.100.128,hostfwd=tcp::${HOST_PORT}-:22 \
    -device virtio-net-device,netdev=net0 \
    -device virtio-rng-pci \
    -smp ${SMP}