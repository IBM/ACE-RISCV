#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
CARGO = cargo
RELEASE = --release
CHAIN=riscv64gc-unknown-linux-gnu
TARGET = --target=$(CHAIN)
RUSTFLAGS = -C linker=riscv64-unknown-linux-gnu-gcc
EXEC_NAME = cove-tap-tool
MAKEFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

ACE_DIR := $(if $(ACE_DIR),$(ACE_DIR),$(MAKEFILE_SOURCE_DIR)../build/target/)

WORK_DIR=$(ACE_DIR)/cove_tap_tool
TOOLS_DIR=$(ACE_DIR)/tools

PLATFORM_RISCV_ABI ?= lp64d
PLATFORM_RISCV_ISA ?= rv64gc
PLATFORM_RISCV_XLEN ?= 64
CROSS_COMPILE ?= riscv64-unknown-linux-gnu-

all: build

build: fmt
	echo "Building Local Attestation utility" ;\
	mkdir -p $(WORK_DIR) ; \
	rm -f $(WORK_DIR)/$(CHAIN)/release/$(EXEC_NAME); \
	RUSTFLAGS='$(RUSTFLAGS)' CARGO_TARGET_DIR=$(WORK_DIR) INSTALL_DIR=$(ACE_DIR)/ $(CARGO) build $(RELEASE) $(TARGET) ; \
	cp $(WORK_DIR)/$(CHAIN)/release/$(EXEC_NAME) $(TOOLS_DIR)/ ;

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
