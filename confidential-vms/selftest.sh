#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

# This script runs all tests in harness

declare -a TESTS=("test_esm")

for i in "${TESTS[@]}"; do
    ./$i.sh 2>&1 > $i.log 
    RESULT=$?
    if [ $RESULT -eq 0 ]; then
        echo "$i: success"
    else
        echo "$i: failed"
        cat $i.log  
    fi
done