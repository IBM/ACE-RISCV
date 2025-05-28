#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
export TVM_TEST_PASSWD="passwd"
export SSH_CMD="sshpass -p ${TVM_TEST_PASSWD} ssh -y -q"

function kill_confidential_vm() {
    PID="$(pidof qemu-system-riscv64)"
    kill -9 $PID
    wait $PID 2>/dev/null
}

function wait_for_ssh () {
    for i in $(seq 1 30); do
        if [ "$( $SSH_CMD -p$3 $1@$2 'whoami' )" == "root" ]; then
            break
        fi
        echo "Waiting for the TVM's SSH ..."
        sleep 1
    done
}
