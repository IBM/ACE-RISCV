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

# execute tests remotely over ssh
${SSH_CMD} -p${HYPERVISOR_TEST_PORT} ${HYPERVISOR_TEST_LOGIN}@${HYPERVISOR_TEST_HOSTNAME} './selftest.sh' > ace_test_results

# kill the VM
kill_qemu ${HYPERVISOR_TEST_PORT}

FAILED="$( grep ': failed' ace_test_results | wc -l)"
cat ace_test_results

if [[ $FAILED -gt 0 ]]; then
    exit 1
fi
exit 0
