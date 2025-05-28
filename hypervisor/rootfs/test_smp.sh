#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
. common.sh

/root/run_linux_vm_qemu.sh -s=2 -m=256M --daemonize 2>&1 > tmp_run_smp.log &
sleep 5

TVM_USER="root"
TVM_HOST="localhost"
TVM_PORT="$(grep 'SSH port' tmp_run_smp.log | awk -F': ' '{ print $2 }' )"
echo "TVM's SSH is listening on port: $TVM_PORT"

wait_for_ssh $TVM_USER $TVM_HOST $TVM_PORT

$SSH_CMD -p${TVM_PORT} ${TVM_USER}@${TVM_HOST} 'cat /root/this_is_confidential_vm_filesystem' > tmp_smp_dmesg.log
RESULT="$(grep 'hello from confidential VM filesystem' tmp_smp_dmesg.log | wc -l)"

kill_confidential_vm
sleep 5

if [[ "x$RESULT" == "x1" ]]; then
    echo "SMP test succeeded"
    exit 0
else
    echo "SMP test failed"
    exit 1
fi
