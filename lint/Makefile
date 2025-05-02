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

export LINT_TOP  := $(TOP)
export PKG_SRCS  := $(shell find $(PWD)/../pkg -name '*.svh')
export RTL_SRCS  := $(shell find $(PWD)/../hdl -name '*.sv')
export DW_IP     := $(shell python3 get_dw_ip.py)
export DW_INC		 := /software/Synopsys-2021_x86_64/syn/R-2020.09-SP4/dw/sim_ver

.PHONY: info
info:
	@echo -e ${GREEN}WELCOME TO THE LINTER!${RESET}
	@echo -e 
	@echo -e ${GREEN}TOP is the top level module in 'chip/digital/rtl/...'${RESET}
	@echo -e ${GREEN}Example: make lint TOP=...${RESET}
	@echo -e 

.PHONY: lint
lint: clean
	mkdir -p reports
	sg_shell < lint.tcl |& tee reports/lint.log
	mv spyglass-1/consolidated_reports/*_lint_lint_turbo_rtl/*.rpt reports/
	mv reports/moresimple_turbo.rpt reports/lint.rpt
	rm -rf spyglass-1 WORK *.log
	bash check_lint_error.sh

.PHONY: clean
clean:
	rm -rf spyglass-1 WORK *.log reports