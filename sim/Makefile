# Variables for UVM
UVM_VERBOSITY := UVM_MEDIUM
TEST ?= 

UVM_HOME := $(PWD)/uvm-1.2

VCS := +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv \
	$(UVM_HOME)/src/dpi/uvm_dpi.cc -CFLAGS -DVCS

SIMV := +UVM_VERBOSITY=$(UVM_VERBOSITY) +UVM_TESTNAME=$(TEST) +UVM_NO_RELNOTES

URG := urg -format text -dir simv.vdbinclude ../Makefile.uvm

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

export CLOCK_PERIOD_PS = $(shell python3 ../synth/get_clock.py)

SHELL=/bin/bash -o pipefail
.SHELLFLAGS += -e

# Directory paths
DIGITAL_PATH := $(PWD)/../chip

# Testbench sources
PKG_SRCS  := $(shell find $(DIGITAL_PATH)/pkg -name '*.svh' -o -name '*.sv')
RTL_SRCS  := $(shell find $(DIGITAL_PATH)/rtl -name '*.sv' -o -name '*.v')
IP_SRCS   := $(shell find $(DIGITAL_PATH)/ip -name '*.sv' -o -name '*.v')
MIXED_SRCS:= $(shell find $(DIGITAL_PATH/spice -name '*.spi'))
IP_INC    := +incdir+$(DIGITAL_PATH)/ip/w25q128jv
VC_SRCS   := $(shell find $(DIGITAL_PATH)/tb/vc/$(DIR) -name '*.sv' -o -name '*.v')
VC_INC    := +incdir+$(DIGITAL_PATH)/tb/vc/$(DIR)
MEM_SRCS  := $(shell find $(DIGITAL_PATH)/memory/output -name '*.v')
CELL_SRCS := $(shell find $(DIGITAL_PATH)/stdcells -name '*.sv' -o -name '*.v')
DW        := /software/Synopsys-2021_x86_64/syn/R-2020.09-SP4/dw
DW_IP     := $(shell python3 get_dw_ip.py)
SRCS      := $(PKG_SRCS) $(RTL_SRCS) $(IP_SRCS) $(VC_SRCS) $(MEM_SRCS) $(DW_IP) $(CELL_SRCS)
CELL_LIB  := $(PWD)/../chip/stdcells/tsmc65_rvt_sc_adv10.v
GATE_SRCS := $(PWD)/../synth/outputs/core.gate.v $(PKG_SRCS)  $(IP_SRCS) $(VC_SRCS) $(MEM_SRCS) $(DW_IP) $(CELL_LIB) $(MIXED_SRCS)
SDF_SRCS  := $(PWD)/../synth/outputs/core.gate.sdf
PNR_GATE_SRCS := $(PWD)/../pnr/outputs/core.pnr.v $(PKG_SRCS)  $(IP_SRCS) $(VC_SRCS) $(MEM_SRCS) $(DW_IP) $(CELL_LIB)
PNR_SDF_SRCS  := $(PWD)/../pnr/outputs/core.pnr.sdf
SYN_GATE_SRCS := $(PWD)/../synth/outputs/core.gate.v $(PKG_SRCS)  $(IP_SRCS) $(VC_SRCS) $(MEM_SRCS) $(DW_IP) $(CELL_LIB)
SYN_SDF_SRCS  := $(PWD)/../synth/outputs/core.gate.sdf
TOP       := $(basename $(notdir $(shell find $(DIGITAL_PATH)/tb/vc/$(DIR) -name 'top_tb**.sv')))

# Toggle UVM
UVM_FLAGS := $(if $(TEST),$(VCS),)

# Command line switches
DEFINE_FLAGS := $(addprefix +define+, $(DEFINE))

# Simulator arguments
export VCS_ARCH_OVERRIDE=linux
VCS_FLAGS := -full64 -lca -sverilog -timescale=1ns/1ps -debug_acc+all -kdb \
-debug_access -suppress=LCA_FEATURES_ENABLED +incdir+$(DW)/sim_ver \
+define+DW_SUPPRESS_WARN \
-xprop=../xprop.config -xprop=flowctrl

# Environment arguments
export PATH := $(PATH):/ece498hk/libs/riscv/bin

.PHONY: info
info:
	@echo -e ${GREEN}WELCOME TO THE CUSTOM TEST SUITE!${RESET}
	@echo -e 
	@echo -e ${GREEN}make vc DIR=... DEFINE=... TEST=...${RESET}
	@echo -e 
	@echo -e ${GREEN}DIR is the name of your directory in 'chip/tb/vc/...'${RESET}
	@echo -e ${GREEN}DEFINE includes any CLI defines to alter testbench behavior${RESET}
	@echo -e ${GREEN}TEST is the name of your UVM test, UVM testbench specific${RESET}
	@echo -e 
	@echo -e ${GREEN}Example: make vc DIR=fifo TEST=fifo_test${RESET}
	@echo -e ${GREEN}Example: make vc DIR=cpu DEFINE=RANDOM TEST=cpu_test ${RESET}
	@echo -e ${GREEN}Example: make vc DIR=cpu DEFINE=RANDOM TEST=cpu_test ${RESET}

sim/top_tb: $(SRCS)
	mkdir -p sim
	python3 ../bin/rvfi_reference.py
	python3 set_dw_ip.py
	cd sim && vcs $(UVM_FLAGS) $(DEFINE_FLAGS) $(SRCS) $(VCS_FLAGS) $(VC_INC) $(IP_INC) \
	+define+ACADIA_SIM +define+ACADIA_ASSERTIONS +define+ACADIA_NOSPEC_STDCELL +notimingcheck \
	+define+ACADIA_NOSPEC_STDCELL \
	-msg_config=../vcs_warn.config -l compile.log -top $(TOP) -o top_tb
	bash check_compile_error.sh

.PHONY: vc
vc: sim/top_tb
	@echo -e ${GREEN}Running Verification Component: $(TOP) @ /chip/tb/vc/$(DIR)${RESET}
	@echo -e ${GREEN}Running UVM TEST: $(TEST)${RESET}
	rm -f sim/dump.fsdb
	python3 ../synth/get_clock.py
	export ECE411_CLOCK_PERIOD_PS=$(shell python3 ../synth/get_clock.py) ;\
	export ECE411_MEMLST=$(PWD)/sim/memory ;\
	export IP_DIR=$(DIGITAL_PATH)/ip ;\
	cd sim && ./top_tb -u -l simulation.log
	bash check_sim_error.sh

sim/top_tb_gl: $(PNR_GATE_SRCS)
	mkdir -p sim
	python3 ../bin/rvfi_reference.py
	python3 set_dw_ip.py
	cd sim && vcs $(UVM_FLAGS) $(DEFINE_FLAGS) $(PNR_GATE_SRCS) $(VCS_FLAGS) $(VC_INC) $(IP_INC) \
	-sdf max:top_tb.dut:$(PNR_SDF_SRCS) +transport_path_delays +pulse_e/0 +pulse_r/0 +neg_tchk \
	+sdfverbose -j4 \
	+transport_int_delays +pulse_int_e/0 +pulse_int_r/0 \
	-diag timescale \
	-msg_config=../vcs_warn.config -l compile.log -top $(TOP) -o top_tb_gl
	bash check_compile_error.sh

sim/top_tb_mixed: $(PNR_GATE_SRCS)
	mkdir -p sim
	python3 ../bin/rvfi_reference.py
	python3 set_dw_ip.py
	cd sim && vcs $(UVM_FLAGS) $(DEFINE_FLAGS) $(PNR_GATE_SRCS) $(VCS_FLAGS) $(VC_INC) $(IP_INC) \
	-ad=/home/jjyun4/acadia/digital/chip/spice/analogTop.init \
	-sdf max:top_tb.dut:$(PNR_SDF_SRCS) +transport_path_delays +pulse_e/0 +pulse_r/0 +neg_tchk \
	+sdfverbose -j4 \
	+transport_int_delays +pulse_int_e/0 +pulse_int_r/0 \
	-diag timescale \
	-msg_config=../vcs_warn.config -l compile.log -top $(TOP) -o top_tb_mixed
	bash check_compile_error.sh


.PHONY: gl
gl: sim/top_tb_gl
	@echo -e ${GREEN}Running Gate-Level Simluation: $(TOP) @ /chip/tb/vc/$(DIR)${RESET}
	rm -f sim/dump.fsdb
	python3 ../synth/get_clock.py
	export ECE411_CLOCK_PERIOD_PS=$(shell python3 ../synth/get_clock.py) ;\
	export ECE411_MEMLST=$(PWD)/sim/memory ;\
	export IP_DIR=$(DIGITAL_PATH)/ip ;\
	cd sim && ./top_tb_gl $(SIMV) -l simulation.log
	bash check_sim_error.sh

.PHONY: mixed
mixed: sim/top_tb_mixed
	@echo -e ${GREEN}Running Gate-Level Simluation: $(TOP) @ /chip/tb/vc/$(DIR)${RESET}
	rm -f sim/dump.fsdb
	python3 ../synth/get_clock.py
	export ECE411_CLOCK_PERIOD_PS=$(shell python3 ../synth/get_clock.py) ;\
	export ECE411_MEMLST=$(PWD)/sim/memory ;\
	export IP_DIR=$(DIGITAL_PATH)/ip ;\
	cd sim && ./top_tb_mixed -ucli -i ../ucli.cmd -l simulation.log
	bash check_sim_error.sh


.PHONY: compile
compile: $(PROG)
	../bin/generate_memory_file.sh $(PROG) $(SPIKE) $(INC)

.PHONY: compare
compare:
	@diff -s sim/commit.log sim/spike.log

.PHONY: cov
covrep: sim/top_tb.vdb
	cd sim && urg -dir top_tb.vdb

.PHONY: verdi
verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/sim/dump.fsdb

.PHONY: verdi_mixed
verdi_mixed:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/sim/out.fsdb

.PHONY: spike
spike: $(ELF)
	mkdir -p sim
	/class/ece411/riscv/bin/spike --isa=rv32imc -m0x60000000:0x01000000,0x70000000:0x00002000 --log-commits $(ELF) |& tail -n +6 > sim/spike.log

.PHONY: interactive_spike
interactive_spike: $(ELF)
	mkdir -p sim
	/class/ece411/riscv/bin/spike --isa=rv32imc -m0x60000000:0x01000000,0x70000000:0x00002000 --log-commits -d $(ELF)

.PHONY: clean
clean:
	rm -rf bin sim verdi

include verilator.mk
