#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

# this script is used for the development process to run the VM/confidential VM
. common.sh

run_confidential_vm "baremetal/baremetal" 2 128M