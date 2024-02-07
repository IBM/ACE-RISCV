#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

. common.sh

run_confidential_vm "baremetal/baremetal" 2 128M
sleep 25 # wait for the test to finish
kill_confidential_vm

result="$(grep 'Hello IBM from confidential VM' guest.log | wc -l)"
if [[ "$result" -ne 1 ]]; then
    exit -1
fi

exit 0