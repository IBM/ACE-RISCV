#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
MAKEFILE_PATH 							:= $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR 					:= $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

export ACE_DIR 							?= $(MAKEFILE_SOURCE_DIR)/build/
# QEMU
export QEMU_SOURCE_DIR					?= $(MAKEFILE_SOURCE_DIR)/qemu/
export QEMU_WORK_DIR					?= $(ACE_DIR)/qemu/
export QEMU_RISCV_WORK_DIR				?= $(ACE_DIR)/qemu-riscv/
# Riscv toolchain
export RISCV_GNU_TOOLCHAIN_SOURCE_DIR	?= $(MAKEFILE_SOURCE_DIR)/riscv-gnu-toolchain/
export RISCV_GNU_TOOLCHAIN_WORK_DIR		?= $(ACE_DIR)/riscv-gnu-toolchain/
# Confidential VMs
export CONFIDENTIAL_VMS_SOURCE_DIR		?= $(MAKEFILE_SOURCE_DIR)/confidential-vms
# Hypervisor
export HYPERVISOR_WORK_DIR				?= $(ACE_DIR)/hypervisor/
export HYPERVISOR_OVERLAY_DIR			?= $(HYPERVISOR_WORK_DIR)/overlay
export HYPERVISOR_OVERLAY_ROOT_DIR		?= $(HYPERVISOR_OVERLAY_DIR)/root
export LINUX_IMAGE						?= $(HYPERVISOR_WORK_DIR)/buildroot/images/Image
# Tools
export TOOLS_SOURCE_DIR					?= $(MAKEFILE_SOURCE_DIR)/tools
export TOOLS_WORK_DIR					?= $(ACE_DIR)/tools

export CROSS_COMPILE					?= riscv64-unknown-linux-gnu-
export PLATFORM_RISCV_XLEN				= 64
export PLATFORM_RISCV_ISA				= rv64gc
export PLATFORM_RISCV_ABI				= lp64d
export PATH 							:= $(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)

all: emulator tools firmware confidential_vms

setup:
	echo $(ACE_DIR)
	@mkdir -p $(ACE_DIR)

devtools: setup
	if [ ! -f "${RISCV_GNU_TOOLCHAIN_WORK_DIR}/bin/${CROSS_COMPILE}gcc" ]; then \
		rm -rf $(RISCV_GNU_TOOLCHAIN_WORK_DIR); \
		mkdir -p $(RISCV_GNU_TOOLCHAIN_WORK_DIR); \
		wget -q https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2023.09.27/riscv64-glibc-ubuntu-22.04-gcc-nightly-2023.09.27-nightly.tar.gz ; \
		tar -zxf riscv64-glibc-ubuntu-22.04-gcc-nightly-2023.09.27-nightly.tar.gz --directory ${RISCV_GNU_TOOLCHAIN_WORK_DIR}/ ; \
		mv ${RISCV_GNU_TOOLCHAIN_WORK_DIR}/riscv/* ${RISCV_GNU_TOOLCHAIN_WORK_DIR}/ ; \
		rm -f riscv64-glibc-ubuntu-22.04-gcc-nightly-2023.09.27-nightly.tar.gz ; \
	fi

hypervisor: setup devtools
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) $(MAKE) -C hypervisor

confidential_vms: setup devtools hypervisor
	BIN_DIR="$(OVERLAY_ROOT_DIR)/" RELEASE="" $(MAKE) -C $(CONFIDENTIAL_VMS_SOURCE_DIR)/baremetal/ ;\
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) $(MAKE) -C $(CONFIDENTIAL_VMS_SOURCE_DIR)/linux_vm/ buildroot ;\
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) $(MAKE) -C $(CONFIDENTIAL_VMS_SOURCE_DIR)/linux_vm/ overlay ;\
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) $(MAKE) -C hypervisor rootfs;

hypervisor_dev: 
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) $(MAKE) -C hypervisor dev

dev:
	$(MAKE) -C $(CONFIDENTIAL_VMS_SOURCE_DIR)/linux_vm/ dev ;\
	$(MAKE) -C $(CONFIDENTIAL_VMS_SOURCE_DIR)/linux_vm/ overlay ;\
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) $(MAKE) -C hypervisor rootfs;

security_monitor: setup devtools
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) LINUX_IMAGE=$(LINUX_IMAGE) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C security-monitor build

firmware: setup devtools hypervisor
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) LINUX_IMAGE=$(LINUX_IMAGE) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C security-monitor opensbi

emulator: setup devtools
	if [ ! -f "${QEMU_WORK_DIR}/bin/qemu-system-riscv64" ]; then \
		mkdir -p $(QEMU_WORK_DIR); \
		cd $(QEMU_SOURCE_DIR); ./configure --prefix=$(QEMU_WORK_DIR) --enable-slirp --enable-kvm --target-list=riscv64-softmmu,riscv64-linux-user; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(QEMU_SOURCE_DIR) >/dev/null; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(QEMU_SOURCE_DIR) install; \
	fi

tools: setup
	mkdir -p $(TOOLS_WORK_DIR)
	cp -rf $(TOOLS_SOURCE_DIR)/* $(TOOLS_WORK_DIR)

verify:
	rm -rf $(ACE_DIR)/security_monitor/verify/
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) LINUX_IMAGE=$(LINUX_IMAGE) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C verification verify

clean:
	rm -rf $(ACE_DIR)

.PHONY: all security-monitor riscv-gnu-toolchain devtools hypervisor firmware emulator tools clean
