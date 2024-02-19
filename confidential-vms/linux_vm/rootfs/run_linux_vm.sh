#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

QEMU_CMD=qemu-system-riscv64
KERNEL=/root/linux_vm/Image
DRIVE=/root/linux_vm/rootfs.ext2

HOST_PORT="$((3000 + RANDOM % 3000))"
INTERACTIVE="-nographic"
SMP=1
MEMORY=1G

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
    ${INTERACTIVE} \
    --enable-kvm \
    -machine virt -cpu rv64 -smp ${SMP} -m ${MEMORY} \
    -kernel ${KERNEL} \
    -global virtio-mmio.force-legacy=false \
    -append "console=ttyS0 ro root=/dev/vda swiotlb=force" \
    -netdev user,id=net0,net=192.168.100.1/24,dhcpstart=192.168.100.128,hostfwd=tcp::${HOST_PORT}-:22 \
    -device virtio-net-pci,netdev=net0 \
    -device virtio-rng-pci \
    -drive if=none,format=raw,file=${DRIVE},id=hd0 \
    -device virtio-blk-pci,drive=hd0 \
    -nographic 
