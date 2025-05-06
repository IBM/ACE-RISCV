.PHONY: run-riscv clean setup-sail-riscv setup-sail-riscv-hext run-riscv-hext setup-plex

default_results_dir="test-results"
default_sail_dir="sail-riscv"
default_sail_hext_dir="riscv-hext-sail"

setup-plex: 
	pip install plex3

setup-sail-riscv:
	git submodule update --init --recursive 
	git checkout 585e6ff5972366075281a416884b6ff3b95bcd62
	$(shell cd sail-riscv/ && git apply ../patches/sail-riscv-csr-access.patch && make csim)
	@echo "Done building the RISC-V Sail model." 

setup-sail-riscv-hext: 
	git submodule update --init --recursive
	git checkout 218c77be8b1dbbe162a949b983680d0ff0181ea9
	$(shell cd riscv-hext-sail/ && git apply ../patches/sail-riscv-hext-csr-access.patch && make csim)
	@echo "Done building the RISC-V Sail model with H-extension." 

run-riscv:
	$(shell mkdir -p $(default_results_dir) && mkdir -p $(default_results_dir)/scanner-results/ && mkdir -p $(default_results_dir)/scanner-results/riscv64/)
	$(shell cd sail-riscv/ && ./c_emulator/riscv_sim_RV64 test/riscv-tests/rv64ui-p-add.elf > ../$(default_results_dir)/scanner-results/riscv64/csr_access.txt)
	python3 src/__main__.py riscv64 $(default_sail_dir) $(default_sail_dir)/model $(default_results_dir) ../rv_gc_traces_full.txt > reproducing_test_results_log.txt

run-riscv-hext: 
	@echo "TODO"

clean:
	rm -rf .pytest_cache
