#!/usr/bin/env bash
# Copyright IBM Corporation 2021, all rights reserved
# Author: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich

MAKEFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))
ACE_DIR := $(if $(ACE_DIR),$(ACE_DIR),$(MAKEFILE_SOURCE_DIR)build/)

CROSS_COMPILE=riscv64-unknown-linux-gnu-

PLATFORM_RISCV_XLEN=64 
PLATFORM_RISCV_ISA=rv64gc 
PLATFORM_RISCV_ABI=lp64d

QEMU_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/qemu/
QEMU_WORK_DIR=$(ACE_DIR)/qemu/
QEMU_RISCV_WORK_DIR=$(ACE_DIR)/qemu-riscv/
RISCV_GNU_TOOLCHAIN_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/riscv-gnu-toolchain/
RISCV_GNU_TOOLCHAIN_WORK_DIR=$(ACE_DIR)/riscv-gnu-toolchain/

HARNESS_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/confidential-vms
CONFIGURATION_DIR=$(MAKEFILE_SOURCE_DIR)/hypervisor/configurations
PATCHES_DIR=$(CONFIGURATION_DIR)/patches
# Hypervisor 
BUILDROOT_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/hypervisor/buildroot
BUILDROOT_WORK_DIR=$(ACE_DIR)/buildroot
BUILDROOT_CONFIG_DIR=$(CONFIGURATION_DIR)/qemu_riscv64_virt_defconfig
OVERLAY_DIR=$(ACE_DIR)/overlay
OVERLAY_ROOT_DIR=$(OVERLAY_DIR)/root
# Linux kernel
LINUX_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/hypervisor/linux/
LINUX_PATCH=$(PATCHES_DIR)/linux/linux-kernel-6.3.0-rc5.patch
LINUX_WORK_DIR=$(ACE_DIR)/linux/
LINUX_IMAGE=$(LINUX_WORK_DIR)/arch/riscv/boot/Image
# Scripts and custom utilities to run/debug the system
TOOLS_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/tools
TOOLS_WORK_DIR=$(ACE_DIR)/tools

export PATH := $(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)

all: devtools hypervisor firmware emulator

devtools: riscv-gnu-toolchain
hypervisor: buildroot linux
firmware: overlay qemu rootfs security-monitor
emulator: qemu tools

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

riscv-gnu-toolchain: setup
	if [ ! -f "${RISCV_GNU_TOOLCHAIN_WORK_DIR}/bin/${CROSS_COMPILE}gcc" ]; then \
		rm -rf $(RISCV_GNU_TOOLCHAIN_WORK_DIR); \
		mkdir -p $(RISCV_GNU_TOOLCHAIN_WORK_DIR); \
		$(MAKE) -C $(RISCV_GNU_TOOLCHAIN_SOURCE_DIR) clean; \
		cd $(RISCV_GNU_TOOLCHAIN_SOURCE_DIR); ./configure --prefix=$(RISCV_GNU_TOOLCHAIN_WORK_DIR) --with-arch=$(PLATFORM_RISCV_ISA) --with-abi=$(PLATFORM_RISCV_ABI); \
		$(MAKE) -C $(RISCV_GNU_TOOLCHAIN_SOURCE_DIR) linux >/dev/null; \
		$(MAKE) -C $(RISCV_GNU_TOOLCHAIN_SOURCE_DIR) linux install >/dev/null; \
	fi

buildroot: setup devtools
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

overlay: devtools hypervisor
	cp $(HARNESS_SOURCE_DIR)/*.sh $(OVERLAY_ROOT_DIR)/; \
	BIN_DIR="$(OVERLAY_ROOT_DIR)/" $(MAKE) -C $(HARNESS_SOURCE_DIR)/baremetal/ debug; \
	cp -r $(HARNESS_SOURCE_DIR)/ace-kernel-module $(OVERLAY_ROOT_DIR)/; \
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -s -C $(OVERLAY_ROOT_DIR)/ace-kernel-module/ CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv KDIR=$(LINUX_SOURCE_DIR)  O=$(LINUX_WORK_DIR) CC="riscv64-unknown-linux-gnu-gcc"
 
rootfs: devtools hypervisor
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -s -C $(BUILDROOT_SOURCE_DIR) RISCV=$(RISCV) PATH=$(PATH) O=$(BUILDROOT_WORK_DIR) rootfs-ext2 

linux: setup patch devtools
	if [ ! -f "${LINUX_IMAGE}" ]; then \
		rm -rf $(LINUX_WORK_DIR); \
		mkdir -p $(LINUX_WORK_DIR); \
		cp $(CONFIGURATION_DIR)/linux64-defconfig $(LINUX_WORK_DIR)/.config; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(LINUX_SOURCE_DIR) O=$(LINUX_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv olddefconfig; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(LINUX_SOURCE_DIR) O=$(LINUX_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv modules >/dev/null; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(LINUX_SOURCE_DIR) O=$(LINUX_WORK_DIR) CROSS_COMPILE=$(CROSS_COMPILE) ARCH=riscv >/dev/null; \
	fi

security-monitor: setup devtools buildroot linux overlay rootfs
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" LINUX_SOURCE_DIR=$(LINUX_SOURCE_DIR) LINUX_WORK_DIR=$(LINUX_WORK_DIR) ACE_DIR=$(ACE_DIR) LINUX_IMAGE=$(LINUX_IMAGE) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C security-monitor opensbi

clippy: setup devtools buildroot linux 
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" LINUX_SOURCE_DIR=$(LINUX_SOURCE_DIR) LINUX_WORK_DIR=$(LINUX_WORK_DIR) ACE_DIR=$(ACE_DIR) LINUX_IMAGE=$(LINUX_IMAGE) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C security-monitor opensbi clippy

qemu: setup devtools
	if [ ! -f "${QEMU_WORK_DIR}/bin/qemu-system-riscv64" ]; then \
		mkdir -p $(QEMU_WORK_DIR); \
		cd $(QEMU_SOURCE_DIR); ./configure --prefix=$(QEMU_WORK_DIR) --target-list=riscv64-softmmu,riscv64-linux-user; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(QEMU_SOURCE_DIR) >/dev/null; \
		PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" $(MAKE) -C $(QEMU_SOURCE_DIR) install; \
	fi 

tools: setup
	mkdir -p $(TOOLS_WORK_DIR)
	cp -rf $(TOOLS_SOURCE_DIR)/* $(TOOLS_WORK_DIR)

call-stack: setup devtools buildroot linux 
	PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" LINUX_SOURCE_DIR=$(LINUX_SOURCE_DIR) LINUX_WORK_DIR=$(LINUX_WORK_DIR) ACE_DIR=$(ACE_DIR) LINUX_IMAGE=$(LINUX_IMAGE) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C security-monitor call-stack 

clean:
	rm -rf $(ACE_DIR)

.PHONY: all security-monitor riscv-gnu-toolchain devtools hypervisor firmware emulator qemu tools buildroot linux clean overlay rootfs
