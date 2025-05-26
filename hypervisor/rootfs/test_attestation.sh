#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
. common.sh

/root/run_linux_vm_qemu.sh --daemonize 2>&1 > tmp_run_vm.log &
sleep 5

TVM_USER="root"
TVM_HOST="localhost"
TVM_PORT="$(grep 'SSH port' tmp_run_vm.log | awk -F': ' '{ print $2 }' )"
echo "TVM's SSH is listening on port: $TVM_PORT"

wait_for_ssh $TVM_USER $TVM_HOST $TVM_PORT

$SSH_CMD -p${TVM_PORT} ${TVM_USER}@${TVM_HOST} 'insmod /root/ace_module/ace.ko'
$SSH_CMD -p${TVM_PORT} ${TVM_USER}@${TVM_HOST} 'dmesg | grep Secret' > tmp_dmesg.log

ATTESTATION_RESULT="$(grep 'Secret=0xc0ffee' tmp_dmesg.log | wc -l)"

kill_confidential_vm

if [[ "x$ATTESTATION_RESULT" == "x1" ]]; then
    echo "Attestation test succeeded"
    exit 0
else
    echo "Attestation test failed"
    exit 1
fi
