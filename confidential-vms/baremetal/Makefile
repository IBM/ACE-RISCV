#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
CARGO 											= cargo
RELEASE 										?= --release
CHAIN											= riscv64gc-unknown-none-elf
TARGET 											= --target=$(CHAIN)
RUSTFLAGS 										= -Clink-arg=-Tsrc/platform/virt.lds -Crelocation-model=pie #-Ccode-model=medium 
EXEC_NAME 										= baremetal

ACE_DIR					 						:= $(if $(ACE_DIR),$(ACE_DIR),$(MAKEFILE_SOURCE_DIR)../../build/)
#
MAKEFILE_PATH 									:= $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR 							:= $(dir $(realpath $(lastword $(MAKEFILE_LIST))))
#
CONFIDENTIAL_VMS_WORK_DIR 						:= $(ACE_DIR)/confidential_vms/
CONFIDENTIAL_VMS_BAREMETAL_WORK_DIR				:= $(CONFIDENTIAL_VMS_WORK_DIR)/baremetal/
#
HYPERVISOR_OVERLAY_DIR							?= $(ACE_DIR)/hypervisor/overlay
HYPERVISOR_OVERLAY_ROOT_DIR						?= $(HYPERVISOR_OVERLAY_DIR)/root
HYPERVISOR_OVERLAY_BAREMETAL_DIR				?= $(HYPERVISOR_OVERLAY_ROOT_DIR)/baremetal
CONFIDENTIAL_VMS_BAREMETAL_ROOTFS_SOURCE_DIR	?= $(MAKEFILE_SOURCE_DIR)/rootfs

all: overlay

build: fmt
	@mkdir -p $(CONFIDENTIAL_VMS_BAREMETAL_WORK_DIR)
	@RUSTFLAGS='$(RUSTFLAGS)' CARGO_TARGET_DIR=$(CONFIDENTIAL_VMS_BAREMETAL_WORK_DIR) INSTALL_DIR=$(HYPERVISOR_OVERLAY_BAREMETAL_DIR) $(CARGO) build $(RELEASE) $(TARGET)

overlay: build
	mkdir -p $(HYPERVISOR_OVERLAY_ROOT_DIR) ;\
	mkdir -p $(CONFIDENTIAL_VMS_BAREMETAL_WORK_DIR) ;\
	cp $(CONFIDENTIAL_VMS_BAREMETAL_ROOTFS_SOURCE_DIR)/*.sh $(HYPERVISOR_OVERLAY_ROOT_DIR)/ ;\
	cp $(CONFIDENTIAL_VMS_BAREMETAL_WORK_DIR)/$(CHAIN)/release/$(EXEC_NAME) $(HYPERVISOR_OVERLAY_BAREMETAL_DIR)/ ;\
	cp $(CONFIDENTIAL_VMS_BAREMETAL_WORK_DIR)/$(CHAIN)/debug/$(EXEC_NAME) $(HYPERVISOR_OVERLAY_BAREMETAL_DIR)/

doc:
	@$(CARGO) doc

check: build test

clippy:
	@$(CARGO) clippy

fmt:
	@$(CARGO) fmt

test:
	@$(CARGO) test

bench:
	@$(CARGO) bench

clean:
	@$(CARGO) clean
	rm -f bin/$(EXEC_NAME)

.PHONY: all build opensbi doc check test bench clean