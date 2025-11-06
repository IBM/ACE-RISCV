#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
MAKEFILE_PATH 							:= $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR 					:= $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

REFINEDRUST_CARGO ?= cargo-refinedrust
REFINEDRUST_RUSTC ?= refinedrust-rustc

REFINEDRUST_GENERATED_DIR ?= generated_code

DUNEFLAGS ?= --display short 

# TODO: currently, this builds in-tree.
# It would be good if we could build in the ACE_DIR
# Main Problem: generating the RefinedRust files there.

## Verification-related make targets

echo_toolchain:
	@echo "Using RefinedRust toolchain located at $(REFINEDRUST_CARGO)"

backup_build_artifacts:
	rm -rf $(REFINEDRUST_GENERATED_DIR).bak
	@[ ! -d $(REFINEDRUST_GENERATED_DIR) ] || (echo "Backing up generated files to $(REFINEDRUST_GENERATED_DIR).bak" && cp -r $(REFINEDRUST_GENERATED_DIR) $(REFINEDRUST_GENERATED_DIR).bak)

generate: echo_toolchain backup_build_artifacts generate_ptrs
	RR_CONFIG=$(MAKEFILE_SOURCE_DIR)/RefinedRust.toml PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C ../security-monitor refinedrust

generate_ptrs:
	cd ../security-monitor/rust-crates/pointers_utility; RR_CONFIG=$(MAKEFILE_SOURCE_DIR)/RefinedRust.toml PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) cargo refinedrust


verify: generate
	@dune build $(DUNEFLAGS) rust_proofs
	@echo "✅︎ Verification succeeded"


clean:
	rm -rf $(ACE_DIR)
	# TODO: clean generated proof files


# generate _CoqProject file
define COQPROJECT_BODY
## theories for manually proved things
-Q _build/default/theories/base/ ace.theories.base
-Q _build/default/theories/page_allocator/ ace.theories.page_allocator
-Q _build/default/theories/page_table/ ace.theories.page_table
-Q _build/default/theories/memory_layout ace.theories.memory_layout

# include RefinedRust-generated theories here
-Q _build/default/$(REFINEDRUST_GENERATED_DIR)/ace sm.ace
endef
export COQPROJECT_BODY

coqproject:
	@echo "$$COQPROJECT_BODY" > _CoqProject
