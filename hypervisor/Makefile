#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
MAKEFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))
ACE_DIR := $(if $(ACE_DIR),$(ACE_DIR),$(MAKEFILE_SOURCE_DIR)../build/)

ROOTFS_SOURCE_DIR				?= $(MAKEFILE_SOURCE_DIR)/rootfs
CONFIGURATION_DIR				?= $(MAKEFILE_SOURCE_DIR)/configurations
BUILDROOT_SOURCE_DIR			?= $(MAKEFILE_SOURCE_DIR)/buildroot
BUILDROOT_WORK_DIR				?= $(ACE_DIR)/buildroot
BUILDROOT_CONFIG_DIR			?= $(CONFIGURATION_DIR)/qemu_riscv64_virt_defconfig
PATCHES_DIR						?= $(CONFIGURATION_DIR)/patches
OVERLAY_DIR						?= $(ACE_DIR)/overlay
OVERLAY_ROOT_DIR				?= $(OVERLAY_DIR)/root
LINUX_SOURCE_DIR				?= $(MAKEFILE_SOURCE_DIR)/linux/
LINUX_PATCH						?= $(PATCHES_DIR)/linux/linux-kernel-6.3.0-rc5.patch
LINUX_WORK_DIR					?= $(ACE_DIR)/linux/
LINUX_IMAGE						?= $(LINUX_WORK_DIR)/arch/riscv/boot/Image

RISCV_GNU_TOOLCHAIN_WORK_DIR	?= $(ACE_DIR)/riscv-gnu-toolchain/
export PATH 					:= $(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)

CROSS_COMPILE					?= riscv64-unknown-linux-gnu-

all: setup buildroot linux

setup:
	env
	uname -a
	echo $(ACE_DIR)
	@mkdir -p $(ACE_DIR)

patch:
	if [ ! -f "${LINUX_SOURCE_DIR}/arch/riscv/kvm/vcpu_sbi_ace.c" ]; then \
		cd $(LINUX_SOURCE_DIR); git apply --whitespace=fix $(LINUX_PATCH); cd $(MAKEFILE_SOURCE_DIR); \
	fi

new_patches:
	cd $(LINUX_SOURCE_DIR); git add . ; git diff HEAD > ../patches/linux/linux-kernel-next.patch; cd $(MAKEFILE_SOURCE_DIR)

buildroot: setup
	if [ ! -f "${BUILDROOT_WORK_DIR}/images/rootfs.ext2" ]; then \
		rm -rf $(BUILDROOT_WORK_DIR); \
		mkdir -p $(BUILDROOT_WORK_DIR); \
		mkdir -p $(OVERLAY_ROOT_DIR); \
		mkdir -p $(OVERLAY_DIR); \
		cp $(BUILDROOT_CONFIG_DIR) $(BUILDROOT_WORK_DIR)/.config; \
		sed "s@^BR2_ROOTFS_OVERLAY=.*@BR2_ROOTFS_OVERLAY=\"$(OVERLAY_DIR)\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
		sed "s@^BR2_TARGET_ROOTFS_EXT2_SIZE=.*@BR2_TARGET_ROOTFS_EXT2_SIZE=\"512M\"@g" -i $(BUILDROOT_WORK_DIR)/.config; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) olddefconfig; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR); \
	fi

overlay:
	mkdir -p $(OVERLAY_ROOT_DIR); \
	mkdir -p $(OVERLAY_DIR); \
	cp $(ROOTFS_SOURCE_DIR)/*.sh $(OVERLAY_ROOT_DIR)/ ; \
	rm -rf $(OVERLAY_ROOT_DIR)/ace-kernel-module/ ; \
	cp -r $(ROOTFS_SOURCE_DIR)/ace-kernel-module $(OVERLAY_ROOT_DIR)/ ; \
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -s -C $(OVERLAY_ROOT_DIR)/ace-kernel-module/ CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv KDIR=$(LINUX_SOURCE_DIR) O=$(LINUX_WORK_DIR) CC="riscv64-unknown-linux-gnu-gcc"
 
rootfs: 
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) rootfs-ext2 

linux: setup patch
	if [ ! -f "${LINUX_IMAGE}" ]; then \
		rm -rf $(LINUX_WORK_DIR); \
		mkdir -p $(LINUX_WORK_DIR); \
		cp $(CONFIGURATION_DIR)/linux64-defconfig $(LINUX_WORK_DIR)/.config; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(LINUX_SOURCE_DIR) O=$(LINUX_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv olddefconfig; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(LINUX_SOURCE_DIR) O=$(LINUX_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv modules >/dev/null; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(LINUX_SOURCE_DIR) O=$(LINUX_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv >/dev/null; \
	fi

clean:
	rm -rf $(ACE_DIR)

.PHONY: all buildroot linux clean overlay rootfs
