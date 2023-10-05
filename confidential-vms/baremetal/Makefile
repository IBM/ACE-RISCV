CARGO = cargo
RELEASE = --release
CHAIN=riscv64gc-unknown-none-elf
TARGET = --target=$(CHAIN)
RUSTFLAGS = -Clink-arg=-Tsrc/platform/virt.lds -Crelocation-model=pie #-Ccode-model=medium 
EXEC_NAME = baremetal
MAKEFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_SOURCE_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

ACE_DIR := $(if $(ACE_DIR),$(ACE_DIR),$(MAKEFILE_SOURCE_DIR)target/)
BIN_DIR := $(if $(BIN_DIR),$(BIN_DIR),$(ACE_DIR)/harness/baremetal/)
TARGET_DIR := $(ACE_DIR)/harness/baremetal/

all: build

build: fmt
	@mkdir -p $(TARGET_DIR)
	@mkdir -p $(BIN_DIR)
	@RUSTFLAGS='$(RUSTFLAGS)' CARGO_TARGET_DIR=$(TARGET_DIR) INSTALL_DIR=$(ACE_DIR) $(CARGO) build $(RELEASE) $(TARGET)
	@cp $(TARGET_DIR)/$(CHAIN)/release/$(EXEC_NAME) $(BIN_DIR)/

debug:
	@mkdir -p $(TARGET_DIR)
	@mkdir -p $(BIN_DIR)
	@RUSTFLAGS='$(RUSTFLAGS)' CARGO_TARGET_DIR=$(TARGET_DIR) INSTALL_DIR=$(ACE_DIR) $(CARGO) build $(TARGET)
	@cp $(TARGET_DIR)/$(CHAIN)/debug/$(EXEC_NAME) $(BIN_DIR)/

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