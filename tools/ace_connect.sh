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

HYPERVISOR_TEST_PORT=$2

${SSH_CMD} -p${HYPERVISOR_TEST_PORT} ${HYPERVISOR_TEST_LOGIN}@${HYPERVISOR_TEST_HOSTNAME}