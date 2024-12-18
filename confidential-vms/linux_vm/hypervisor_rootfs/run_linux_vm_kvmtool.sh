#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0

KERNEL=/root/linux_vm/Image
TAP=/root/linux_vm/tap

./lkvm-static run -c2 --console virtio --cove-vm --cove-tap=${TAP} --cove-single-step-init -p "console=ttyS0 ro root=/dev/vda swiotlb=mmnn,force" -k ${KERNEL} --virtio-transport=pci
