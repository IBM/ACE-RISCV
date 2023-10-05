#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

function run_baremetal() {
    fallocate -l 128M hdd.dsk

    qemu-system-riscv64 -machine virt -cpu rv64 -smp 1 -m 128M \
        --enable-kvm \
        -drive if=none,format=raw,file=hdd.dsk,id=foo \
        -device virtio-blk-device,scsi=off,drive=foo -nographic -bios none \
        -device virtio-rng-device \
        -kernel baremetal &
}

function kill_baremetal() {
    PID="$(pidof qemu-system-riscv64)"
    kill -9 $PID
    wait $PID 2>/dev/null
}

