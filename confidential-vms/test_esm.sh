#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

. common.sh

run_baremetal
sleep 15 # wait for the test to finish
kill_baremetal

result="$(grep 'Hello IBM from confidential VM' guest.log | wc -l)"
if [[ "$result" -ne 1 ]]; then
    exit -1
fi

exit 0