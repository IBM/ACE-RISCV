#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

if [ -z ${ACE_DIR} ]; then
    echo "ACE_DIR must point to the directory where ACE is installed"
    exit 1
fi

# load common configuration
. common.sh

# start the VM
${ACE_DIR}/tools/ace_run_hypervisor.sh --daemonize > .run_tests.log

# find out on which port its ssh server is listening
HYPERVISOR_TEST_PORT="$(grep 'SSH port' .run_tests.log | awk -F': ' '{ print $2 }' )"
echo "Hypervisor's SSH is listening on port: $HYPERVISOR_TEST_PORT"

# wait until the VM is up and running
wait_for_ssh ${HYPERVISOR_TEST_LOGIN} ${HYPERVISOR_TEST_HOSTNAME} ${HYPERVISOR_TEST_PORT}

# test confidential memory protections
QEMU_MEMORY_SIZE_MB=2048

# Verify that the hypervisor has no access to the confidential memory
MEMORY_ACCESS_EXEC="insmod ace-kernel-module/ace.ko"
MEMORY_BASE_ADDRESS="$(hex2dec 80000000 10 16)"
let MEMORY_SIZE=${QEMU_MEMORY_SIZE_MB}*1024*1024
let NONSECURE_MEMORY_BASE_ADDRESS=${MEMORY_BASE_ADDRESS}+2048*1024 # after OpenSBI reserved memory
let SECURE_MEMORY_BASE_ADDRESS=${MEMORY_BASE_ADDRESS}+${MEMORY_SIZE}/2
let SECURE_MEMORY_END_ADDRESS=${SECURE_MEMORY_BASE_ADDRESS}+${MEMORY_SIZE}/2-1

declare -A EXPECTED_MEMORY_ACCESS=([$NONSECURE_MEMORY_BASE_ADDRESS]=0 [$MEMORY_BASE_ADDRESS]=1 [$SECURE_MEMORY_BASE_ADDRESS]=1 [$SECURE_MEMORY_END_ADDRESS]=1)

for i in "${!EXPECTED_MEMORY_ACCESS[@]}"; do
    ADDRESS=$(hex2dec $i 16 10)
    EXPECTED_RESULT=${EXPECTED_MEMORY_ACCESS[$i]}
    RESULT=$(${SSH_CMD} -p${HYPERVISOR_TEST_PORT} ${HYPERVISOR_TEST_LOGIN}@${HYPERVISOR_TEST_HOSTNAME} ./test_secure_memory.sh 0x$ADDRESS 2>&1)
    ACCESS_FAILED="$(echo $RESULT | grep 'Segmentation fault' | wc -l)"
    if [ $ACCESS_FAILED -ne $EXPECTED_RESULT ]; then
        echo "incorrect access rights to $ADDRESS: FAIL"
    else
        echo "correct access rights to $ADDRESS: succeess"
    fi
    kill_qemu ${HYPERVISOR_TEST_PORT}
    ${ACE_DIR}/tools/ace_run_hypervisor.sh --daemonize > .run_tests.log
    HYPERVISOR_TEST_PORT="$(grep 'SSH port' .run_tests.log | awk -F': ' '{ print $2 }' )"
    wait_for_ssh ${HYPERVISOR_TEST_LOGIN} ${HYPERVISOR_TEST_HOSTNAME} ${HYPERVISOR_TEST_PORT}    
done

# execute tests remotely over ssh
${SSH_CMD} -p${HYPERVISOR_TEST_PORT} ${HYPERVISOR_TEST_LOGIN}@${HYPERVISOR_TEST_HOSTNAME} './selftest.sh'

# kill the VM
kill_qemu ${HYPERVISOR_TEST_PORT}
