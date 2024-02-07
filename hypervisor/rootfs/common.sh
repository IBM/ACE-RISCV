#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

function run_confidential_vm() {
    fallocate -l 128M hdd.dsk

    KERNEL_IMAGE=$1
    NUMBER_OF_CORES=$2
    MEMORY_SIZE=$3

    qemu-system-riscv64 -machine virt -cpu rv64 -smp $NUMBER_OF_CORES -m $MEMORY_SIZE \
        --enable-kvm \
        -drive if=none,format=raw,file=hdd.dsk,id=foo \
        -device virtio-blk-device,scsi=off,drive=foo -nographic -bios none \
        -device virtio-rng-device \
        -kernel $KERNEL_IMAGE &
}

function kill_confidential_vm() {
    PID="$(pidof qemu-system-riscv64)"
    kill -9 $PID
    wait $PID 2>/dev/null
}

