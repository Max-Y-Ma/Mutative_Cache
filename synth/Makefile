SHELL=/bin/bash -o pipefail
.SHELLFLAGS += -e

# Define ANSI Color Escape Codes
BOLD='\033[1m'
RED='\033[1;31m'
GREEN='\033[1;32m'
YELLOW='\033[1;33m'
BLUE='\033[1;34m'
MAGENTA='\033[1;35m'
CYAN='\033[1;36m'
WHITE='\033[1;37m'
RESET='\033[0m' # Reset text attributes to default

FSDB2SAIF_START = $(shell head -n1 ../sim/sim/time.txt)
FSDB2SAIF_END   = $(shell tail -n1 ../sim/sim/time.txt)

# Directory paths
export SYNTH_TOP := $(TOP)
export PKG_SRCS  := $(shell find $(PWD)/../pkg -name '*.svh' -o -name '*.sv')
export RTL_SRCS  := $(shell find $(PWD)/../hdl -name '*.sv')
export SRAM_SRCS := $(shell find $(PWD)/../sram/output/ -name '*.v')
export SRAM_LIB  := $(shell find $(PWD)/../sram/output/ -name '*.db')

export STD_CELL_LIB=$(FREEPDK45)/stdcells.db
export STD_CELL_ALIB=$(FREEPDK45)/alib

.PHONY: synth
synth: clean
	$(MAKE) outputs/synth.ddc

outputs/synth.ddc:
	mkdir -p reports outputs
	python3 get_clock.py
	python3 get_min_power.py
	python3 get_compile_cmd.py
	export SYNTH_TOP=$(TOP) ;\
	export PKG_SRCS="$(shell find $(PWD)/../pkg -name '*.svh' -o -name '*.sv')" ;\
	export RTL_SRCS="$(shell find $(PWD)/../hdl -name '*.sv')" ;\
	export SRAM_SRCS="$(shell find $(PWD)/../sram/output/ -name '*.v')" ;\
	export SRAM_LIB="$(shell find $(PWD)/../sram/output/ -name '*.db')" ;\
	export STD_CELL_LIB=$(FREEPDK45)/stdcells.db ;\
	export STD_CELL_ALIB=$(FREEPDK45)/alib ;\
	export ECE411_CLOCK_PERIOD_PS=$(shell python3 get_clock.py) ;\
	export ECE411_MIN_POWER=$(shell python3 get_min_power.py) ;\
	export ECE411_COMPILE_CMD="$(shell python3 get_compile_cmd.py)" ;\
	dc_shell -f synthesis.tcl |& tee reports/synthesis.log
	rm -f  *.log
	rm -f  default.svf
	rm -rf work
	bash check_synth_error.sh


.PHONY: info
info:
	@echo -e ${GREEN}WELCOME TO THE SYNTHESIZER!${RESET}
	@echo -e 
	@echo -e ${GREEN}TOP is the top level module in 'hdl/...'${RESET}
	@echo -e ${GREEN}Example: make synth TOP=...${RESET}
	@echo -e 


../sim/sim/dump.fsdb.saif: ../sim/sim/dump.fsdb
	cd ../sim/sim && fsdb2saif dump.fsdb -bt $(FSDB2SAIF_START)ps -et $(FSDB2SAIF_END)ps -s top_tb/dut

.PHONY: power
power: outputs/synth.ddc ../sim/sim/dump.fsdb.saif
	dc_shell -f power.tcl |& tee reports/power.log

.PHONY: dv
dv:
	design_vision -f dc-gui.tcl

.PHONY: clean
clean:
	rm -f  *.log
	rm -f  default.svf
	rm -rf work
	rm -rf reports
	rm -rf outputs

.PHONY: precheck
precheck:
	@echo -e "$(CYAN)Checking source files...$(RESET)"
	@pkg_count=$$(find $(PWD)/../pkg -name '*.svh' -o -name '*.sv' | wc -l) ; \
	 rtl_count=$$(find $(PWD)/../hdl -name '*.sv' | wc -l) ; \
	 sram_count=$$(find $(PWD)/../sram/output/ -name '*.v' | wc -l) ; \
	 echo "Found $${pkg_count} PKG files." ; \
	 echo "Found $${rtl_count} RTL files." ; \
	 echo "Found $${sram_count} SRAM files." ; \
	 if [ "$${pkg_count}" -eq 0 ]; then echo -e "$(RED)ERROR: No package source files found in ../pkg/.$(RESET)"; exit 1; fi ; \
	 if [ "$${rtl_count}" -eq 0 ]; then echo -e "$(RED)ERROR: No RTL source files found in ../hdl/.$(RESET)"; exit 1; fi ; \
	 if [ "$${sram_count}" -eq 0 ]; then echo -e "$(YELLOW)WARNING: No SRAM source files found in ../sram/output/. Continuing...$(RESET)"; fi


