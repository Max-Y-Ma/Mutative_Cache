VER_DIR := $(DIGITAL_PATH)/hvl/verilator
VER_CFG := $(DIGITAL_PATH)/hvl/verilator/config.vlt
VER_SRC := $(shell find $(DIGITAL_PATH)/hvl/verilator -name '*.sv' -o -name '*.v')
VER_CPP := $(VER_DIR)/top_tb.cpp

VERILATOR_SRCS := $(VER_CFG) $(VER_SRC) $(PKG_SRCS) $(RTL_SRCS) $(SRAM_SRCS) $(MEM_SRCS) $(DW_IP)
VERILATOR_INCS := -I$(DW)/sim_ver -I$(VER_DIR)

START_CYCLE ?= -1
END_CYCLE   ?= 100

export VERILATOR_ROOT=$(PWD)/../verilator

.PHONY: verilator
verilator: $(VERILATOR_SRCS)
	python3 ../bin/rvfi_reference.py
	mkdir -p sim
	cd sim && $(PWD)/../verilator/bin/verilator --x-initial 0 +define+DW_SUPPRESS_WARN \
	-Wall -Wno-UNUSEDPARAM -Wno-UNUSEDSIGNAL -Wno-BLKSEQ -Wno-WIDTHTRUNC \
	-Wno-GENUNNAMED -Wno-WIDTHEXPAND --trace --trace-structs --timescale 1ps/1ps \
	-Dclock_period_ps=$(CLOCK_PERIOD_PS) $(VERILATOR_SRCS) $(VERILATOR_INCS) \
	--top-module verilator_tb -Mdir verilator --cc --exe --build $(VER_CPP)
	cd sim/verilator &&	$(MAKE) -f Vverilator_tb.mk

.PHONY: verilator_run
verilator_run: verilator
	cd sim ;\
	./verilator/Vverilator_tb $(CLOCK_PERIOD_PS) memory_8.lst $(START_CYCLE) $(END_CYCLE)

.PHONY: verilator_manual
verilator_manual: sim/verilator/Vverilator_tb
	cd sim ;\
	./verilator/Vverilator_tb $(CLOCK_PERIOD_PS) $(MEMFILE) $(START_CYCLE) $(END_CYCLE)
