#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

# ssh utilities
export HYPERVISOR_TEST_LOGIN="root"
export HYPERVISOR_TEST_PASSWD="passwd"
export HYPERVISOR_TEST_HOSTNAME="localhost"

export SSH_PASSWD_PARAMS="-o PasswordAuthentication=yes -o PreferredAuthentications=keyboard-interactive,password -o PubkeyAuthentication=no -o StrictHostKeyChecking=no"
export SSH_CMD="sshpass -p ${HYPERVISOR_TEST_PASSWD} ssh ${SSH_PASSWD_PARAMS}"

# Usage: wait_for_ssh "root", "localhost", "22"
function wait_for_ssh () {
    while [ "$( $SSH_CMD -p$3 $1@$2 'whoami' )" != "root" ]; do
        echo "waiting for the hypervisor's ssh ..."
        sleep 1
    done
}

function kill_users_qemu () {
    USER="$(whoami)"
    PID="$(ps aux | grep qemu | grep ${USER} | awk -F' ' '{ print $2  }')"
    if [ "$PID" != "" ]; then
        kill -9 $PID
        wait $PID 2>/dev/null
    fi
}

# Usage: kill_qemu "22"
function kill_qemu () {
    PORT=$1
    PID="$(ps aux | grep qemu | grep ${PORT} | awk -F' ' '{ print $2  }')"
    if [ "$PID" != "" ]; then
        kill -9 $PID
        wait $PID 2>/dev/null
    fi
}
