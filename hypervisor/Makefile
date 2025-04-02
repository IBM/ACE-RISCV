#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
MAKEFILE_PATH 						:= $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR 				:= $(dir $(realpath $(lastword $(MAKEFILE_LIST))))
ACE_DIR 							:= $(if $(ACE_DIR),$(ACE_DIR),$(MAKEFILE_SOURCE_DIR)../build/)
HYPERVISOR_WORK_DIR 				:= $(ACE_DIR)/hypervisor/

HYPERVISOR_ROOTFS_SOURCE_DIR		?= $(MAKEFILE_SOURCE_DIR)/rootfs
HYPERVISOR_CONFIGURATION_DIR		?= $(MAKEFILE_SOURCE_DIR)/configurations
BUILDROOT_SOURCE_DIR				?= $(MAKEFILE_SOURCE_DIR)/buildroot

HYPERVISOR_BUILDROOT_CONFIG_DIR		?= $(HYPERVISOR_CONFIGURATION_DIR)/qemu_riscv64_virt_defconfig
HYPERVISOR_LINUX_CONFIG				?= $(HYPERVISOR_CONFIGURATION_DIR)/linux64-defconfig
HYPERVISOR_BUILDROOT_OVERRIDE_DIR 	?= $(HYPERVISOR_CONFIGURATION_DIR)/package_override.dev
HYPERVISOR_ROOTFS_SIZE				?= "1G"
HYPERVISOR_OVERLAY_DIR				?= $(HYPERVISOR_WORK_DIR)/overlay
HYPERVISOR_OVERLAY_ROOT_DIR			?= $(HYPERVISOR_OVERLAY_DIR)/root
HYPERVISOR_PATCHES_DIR				?= $(MAKEFILE_SOURCE_DIR)/patches
HYPERVISOR_LINUX_PATCH				?= $(HYPERVISOR_PATCHES_DIR)/linux/6.3-rc4/

KVMTOOL_WORK_DIR					?= $(HYPERVISOR_WORK_DIR)/kvmtool

BUILDROOT_WORK_DIR					?= $(HYPERVISOR_WORK_DIR)/buildroot
RISCV_GNU_TOOLCHAIN_WORK_DIR		?= $(ACE_DIR)/riscv-gnu-toolchain/
export PATH 						:= $(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)

CROSS_COMPILE						?= riscv64-unknown-linux-gnu-

all: setup buildroot

setup:
	@mkdir -p $(ACE_DIR)

buildroot: setup
	if [ ! -f "${BUILDROOT_WORK_DIR}/images/rootfs.ext2" ]; then \
		echo "Building the hypervisor with buildroot"; \
		rm -rf $(BUILDROOT_WORK_DIR); \
		mkdir -p $(BUILDROOT_WORK_DIR); \
		mkdir -p $(HYPERVISOR_OVERLAY_ROOT_DIR); \
		mkdir -p $(HYPERVISOR_OVERLAY_DIR); \
		cp $(HYPERVISOR_BUILDROOT_CONFIG_DIR) $(BUILDROOT_WORK_DIR)/.config; \
		echo $(BUILDROOT_WORK_DIR)/.config; \
		sed "s@^BR2_ROOTFS_OVERLAY=.*@BR2_ROOTFS_OVERLAY=\"$(HYPERVISOR_OVERLAY_DIR)\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
		sed "s@^BR2_TARGET_ROOTFS_EXT2_SIZE=.*@BR2_TARGET_ROOTFS_EXT2_SIZE=\"$(HYPERVISOR_ROOTFS_SIZE)\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
		sed "s@^BR2_LINUX_KERNEL_CUSTOM_CONFIG_FILE=.*@BR2_LINUX_KERNEL_CUSTOM_CONFIG_FILE=\"$(HYPERVISOR_LINUX_CONFIG)\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
		sed "s@^BR2_LINUX_KERNEL_PATCH=.*@BR2_LINUX_KERNEL_PATCH=\"$(HYPERVISOR_LINUX_PATCH)\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
		if [ ! -f "$(BUILDROOT_SOURCE_DIR)/Makefile" ]; then \
			echo "Buildroot repository not initialized. Did you forget to run: git submodule update --init --recursive?" ;\
			exit 1 ;\
		fi ;\
		$(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV_GNU_TOOLCHAIN_WORK_DIR) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) BR2_JLEVEL=0 olddefconfig ;\
		$(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV_GNU_TOOLCHAIN_WORK_DIR) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) BR2_JLEVEL=0 ;\
	fi

overlay: kvmtool
	echo "Setting up the content of the hypervisor's root directory" ;\
	mkdir -p $(HYPERVISOR_OVERLAY_ROOT_DIR); \
	mkdir -p $(HYPERVISOR_OVERLAY_DIR); \
	cp $(HYPERVISOR_ROOTFS_SOURCE_DIR)/*.sh $(HYPERVISOR_OVERLAY_ROOT_DIR)/; \
	cp ${KVMTOOL_WORK_DIR}/kvmtool/lkvm-static $(HYPERVISOR_OVERLAY_ROOT_DIR)/;

dev:
	sed "s@^BR2_PACKAGE_OVERRIDE_FILE=.*@BR2_PACKAGE_OVERRIDE_FILE=\"$(HYPERVISOR_BUILDROOT_OVERRIDE_DIR)\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
	sed "s@^BR2_LINUX_KERNEL_CUSTOM_CONFIG_FILE=.*@BR2_LINUX_KERNEL_CUSTOM_CONFIG_FILE=\"$(HYPERVISOR_LINUX_CONFIG)\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
	$(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV_GNU_TOOLCHAIN_WORK_DIR) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) BR2_JLEVEL=0 linux-rebuild all; \
	#$(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV_GNU_TOOLCHAIN_WORK_DIR) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) BR2_JLEVEL=0 qemu-rebuild all

rootfs: overlay
	echo "Generating hypervisor's root filesystem" ;\
	$(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV_GNU_TOOLCHAIN_WORK_DIR) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) rootfs-ext2

kvmtool:
	mkdir -p $(KVMTOOL_WORK_DIR) && cd $(KVMTOOL_WORK_DIR) ;\
    if [ ! -f "${KVMTOOL_WORK_DIR}/dtc/build/libfdt.so" ]; then \
        rm -rf ${KVMTOOL_WORK_DIR}/dtc ;\
        git clone git://git.kernel.org/pub/scm/utils/dtc/dtc.git ;\
        cd dtc ;\
        ARCH=riscv CC="${CROSS_COMPILE}gcc -mabi=${PLATFORM_RISCV_ABI} -march=${PLATFORM_RISCV_ISA}" make NO_PYTHON=1 NO_YAML=1 DESTDIR=$($CC -print-sysroot) PREFIX=${KVMTOOL_WORK_DIR}/dtc/build LIBDIR=${KVMTOOL_WORK_DIR}/dtc/build/$($CC -dumpmachine) install-lib install-includes ;\
        cp ${KVMTOOL_WORK_DIR}/dtc/build/include/* ${KVMTOOL_WORK_DIR}/dtc/build/ ;\
        cd .. ;\
    fi ;\
	if [ ! -f "${KVMTOOL_WORK_DIR}/kvmtool/lkvm-static" ]; then \
		rm -rf ${KVMTOOL_WORK_DIR}/kvmtool ;\
		git clone -b cove-integration-03072023 https://github.com/wojciechozga/kvmtool.git ;\
		rm -f $(KVMTOOL_WORK_DIR)/kvmtool/lkvm-static ;\
		cd $(KVMTOOL_WORK_DIR)/kvmtool ;\
		ARCH=riscv LIBFDT_DIR=${KVMTOOL_WORK_DIR}/dtc/build/ make lkvm-static -j$(nproc) ;\
		${CROSS_COMPILE}strip lkvm-static ;\
		cd .. ;\
	fi

clean:
	rm -rf $(HYPERVISOR_WORK_DIR)

.PHONY: all buildroot linux clean overlay rootfs
