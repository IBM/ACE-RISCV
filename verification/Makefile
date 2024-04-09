#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
MAKEFILE_PATH 							:= $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR 					:= $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

REFINEDRUST_CARGO ?= cargo-refinedrust
REFINEDRUST_RUSTC ?= refinedrust-rustc

# TODO: currently, this builds in-tree.
# It would be good if we could build in the ACE_DIR
# Main Problem: generating the RefinedRust files there.

## Verification-related make targets

echo_toolchain:
	@echo "Using RefinedRust toolchain located at $(REFINEDRUST_CARGO)"

backup_build_artifacts:
	rm -rf generated_code.bak
	@[ ! -d generated_code ] || (echo "Backing up generated files to generated_code.bak" && cp -r generated_code generated_code.bak)

generate: echo_toolchain backup_build_artifacts
	RR_CONFIG=$(MAKEFILE_SOURCE_DIR)/RefinedRust.toml PATH="$(RISCV_GNU_TOOLCHAIN_WORK_DIR)/bin:$(PATH)" ACE_DIR=$(ACE_DIR) CROSS_COMPILE=$(CROSS_COMPILE) PLATFORM_RISCV_XLEN=$(PLATFORM_RISCV_XLEN) PLATFORM_RISCV_ISA=$(PLATFORM_RISCV_ISA) PLATFORM_RISCV_ABI=$(PLATFORM_RISCV_ABI) $(MAKE) -C ../security-monitor refinedrust

verify: generate
	@dune build --display short
	@echo "✅︎ Verification succeeded"


clean:
	rm -rf $(ACE_DIR)
	# TODO: clean generated proof files


# generate _CoqProject file
define COQPROJECT_BODY
## theories for manually proved things
-Q _build/default/theories/memory_tracker/page/ ace.theories.page
-Q _build/default/theories/memory_tracker/page_allocator ace.theories.page_allocator
-Q _build/default/theories/result ace.theories.result
-Q _build/default/theories/memory_layout ace.theories.memory_layout

# include RefinedRust-generated theories here
-Q _build/default/generated_code/ace sm.ace
endef
export COQPROJECT_BODY

coqproject:
	@echo "$$COQPROJECT_BODY" > _CoqProject
