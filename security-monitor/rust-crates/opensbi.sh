#!/usr/bin/env bash
# Copyright IBM Corporation 2022, all rights reserved
# Author: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich

# Description: This script builds OpenSBI from sources

set -e

CURRENT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
NAME=${NAME:-"opensbi"}
VERSION="rust-bindings"

if [ -z ${INSTALL_DIR} ]; then
    echo "INSTALL_DIR must point to the directory where the ${NAME} will be installed!"
    exit 1
fi

if [ -z ${OPENSBI_SOURCE_DIR} ]; then
    echo "OPENSBI_SOURCE_DIR must point to the directory where the opensbi sources are"
    exit 1
fi

WORK_DIR="${INSTALL_DIR}/${NAME}-${VERSION}"
BUILD_DIR="${WORK_DIR}/build"

if [ -f "${WORK_DIR}/lib/libsbi.a" ]; then
    exit 0
fi

rm -rf ${WORK_DIR}
mkdir -p ${WORK_DIR}

cd ${OPENSBI_SOURCE_DIR}/

make PLATFORM_RISCV_XLEN=${PLATFORM_RISCV_XLEN} PLATFORM_RISCV_ISA=${PLATFORM_RISCV_ISA} PLATFORM_RISCV_ABI=${PLATFORM_RISCV_ABI} CROSS_COMPILE=${CROSS_COMPILE} O=${WORK_DIR} PLATFORM=generic -j$(nproc)
make PLATFORM_RISCV_XLEN=${PLATFORM_RISCV_XLEN} PLATFORM_RISCV_ISA=${PLATFORM_RISCV_ISA} PLATFORM_RISCV_ABI=${PLATFORM_RISCV_ABI} CROSS_COMPILE=${CROSS_COMPILE} I=${WORK_DIR} PLATFORM=generic install  -j$(nproc)

echo "export PATH=${WORK_DIR}/lib:${WORK_DIR}/bin:\${PATH}" >> ${INSTALL_DIR}/env
