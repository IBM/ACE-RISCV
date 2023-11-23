#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2023 IBM Corporation
# SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
# SPDX-License-Identifier: Apache-2.0
MAKEFILE_PATH 							:= $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR 					:= $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

REFINEDRUST ?= refinedrust_translate

# TODO: currently, this builds in-tree.
# It would be good if we could build in the ACE_DIR
# Main Problem: generating the RefinedRust files there.

## Verification-related make targets
# a list of Rust source files to verify
VERIFICATION_TARGETS =
# ../security-monitor/src/core/memory_tracker/test.rs

# generate the Coq code for a particular Rust file
# TODO: configure output directory for Refinedrust
%.rs.gen: %.rs
	@$(REFINEDRUST) $<
.PHONY: phony

# generate Coq code for all verification targets
generate_all: $(addsuffix .gen, $(VERIFICATION_TARGETS))
.PHONY: generate_all

echo_toolchain:
	@echo "Using RefinedRust toolchain located at $(REFINEDRUST)"

verify: echo_toolchain generate_all
	@dune build --display short

clean:
	rm -rf $(ACE_DIR)
	# TODO: clean generated proof files
