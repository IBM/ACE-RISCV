#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
CARGO = cargo
RELEASE = --release
CHAIN=riscv64gc-unknown-none-elf
TARGET = --target=$(CHAIN)
RUSTFLAGS = -Clink-arg=-Tsrc/platform/qemu/virt.lds -Crelocation-model=pie #-Ccode-model=medium 
EXEC_NAME = libace.a
MAKEFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

ACE_DIR := $(if $(ACE_DIR),$(ACE_DIR),$(MAKEFILE_SOURCE_DIR)../build/target/)

SM_WORK_DIR=$(ACE_DIR)/security-monitor
PLATFORM_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/platform
OPENSBI_SOURCE_DIR=$(MAKEFILE_SOURCE_DIR)/opensbi
OPENSBI_WORK_DIR=$(SM_WORK_DIR)/opensbi
OPENSBI_SYS_WORK_DIR=$(SM_WORK_DIR)/opensbi_bindings
OPENSBI_PATCH = $(PLATFORM_SOURCE_DIR)/opensbi_v1.4.patch

PLATFORM_RISCV_ABI ?= lp64d 
PLATFORM_RISCV_ISA ?= rv64gc
PLATFORM_RISCV_XLEN ?= 64 
CROSS_COMPILE ?= riscv64-unknown-linux-gnu-

all: audit opensbi_bindings build

build: opensbi_bindings fmt
	echo "Generating OpenSBI bindings" ;\
	mkdir -p $(SM_WORK_DIR) ; \
	rm -f $(SM_WORK_DIR)/$(CHAIN)/release/$(EXEC_NAME); \
	RUSTFLAGS='$(RUSTFLAGS)' CARGO_TARGET_DIR=$(SM_WORK_DIR) INSTALL_DIR=$(ACE_DIR) $(CARGO) build $(RELEASE) $(TARGET) --features verbose ; \
	cp $(SM_WORK_DIR)/$(CHAIN)/release/$(EXEC_NAME) $(SM_WORK_DIR)/ ; \
	rm -rf $(OPENSBI_WORK_DIR)/

refinedrust:
	RUSTFLAGS='$(RUSTFLAGS)' CARGO_TARGET_DIR=$(SM_WORK_DIR) INSTALL_DIR=$(ACE_DIR) $(CARGO) refinedrust $(RELEASE) $(TARGET) --features verbose

debug: opensbi_bindings
	echo "Compiling the security monitor in DEBUG mode" ;\
	mkdir -p $(SM_WORK_DIR) ; \
	rm -f $(SM_WORK_DIR)/$(CHAIN)/debug/$(EXEC_NAME); \
	RUSTFLAGS='$(RUSTFLAGS)' CARGO_TARGET_DIR=$(SM_WORK_DIR) INSTALL_DIR=$(ACE_DIR) $(CARGO) build $(TARGET) --features verbose ; \
	cp $(SM_WORK_DIR)/$(CHAIN)/debug/$(EXEC_NAME) $(SM_WORK_DIR)/ ; \
	rm -rf $(OPENSBI_WORK_DIR)/

opensbi: build
	echo "Compiling OpenSBI" ;\
	if ! grep -q ace_setup_this_hart "$(OPENSBI_SOURCE_DIR)/lib/sbi/sbi_hart.c"; then \
		echo "Applying patches to OpenSBI" ;\
		cd $(OPENSBI_SOURCE_DIR); git apply --whitespace=fix $(OPENSBI_PATCH); cd $(MAKEFILE_SOURCE_DIR);\
	fi ;\
	if [ -f "$(SM_WORK_DIR)/$(CHAIN)/release/$(EXEC_NAME)" ]; then \
		mkdir -p $(OPENSBI_WORK_DIR) ;\
		SM_WORK_DIR=$(SM_WORK_DIR) $(MAKE) -j$(nproc) -C $(OPENSBI_SOURCE_DIR) O=$(OPENSBI_WORK_DIR) PLATFORM_DIR="$(PLATFORM_SOURCE_DIR)" PLATFORM="generic" CROSS_COMPILE=$(CROSS_COMPILE) FW_PAYLOAD_PATH=$(LINUX_IMAGE) FW_PAYLOAD=y PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI); \
	fi

opensbi_bindings:
	echo "Compiling OpenSBI bindings" ;\
	if grep -q ace_setup_this_hart "$(OPENSBI_SOURCE_DIR)/lib/sbi/sbi_hart.c"; then \
		echo "Applying patches to OpenSBI bindings" ;\
		cd $(OPENSBI_SOURCE_DIR); git apply -R --whitespace=fix $(OPENSBI_PATCH); cd $(MAKEFILE_SOURCE_DIR); \
	fi; \
	INSTALL_DIR=$(ACE_DIR) OPENSBI_SOURCE_DIR=$(OPENSBI_SOURCE_DIR) CROSS_COMPILE=$(CROSS_COMPILE) ./rust-crates/opensbi.sh

doc:
	@$(CARGO) doc

check: build test

audit:
	@$(CARGO) audit

clippy:
	@$(CARGO) clippy

fmt:
	@$(CARGO) fmt

bench:
	@$(CARGO) bench

clean:
	@$(CARGO) clean
	rm -f bin/$(EXEC_NAME)

.PHONY: all build hack opensbi doc check test bench clean
