OBJECTS = $(notdir $(basename $(wildcard $(PWD)/config/*.py)))

SHELL=/bin/bash -o pipefail
.SHELLFLAGS += -e

export PYTHONDONTWRITEBYTECODE=1
export PYTHONUNBUFFERED=1

export OPENRAM_PATH=$(PWD)/../OpenRAM
export CONDA_HOME=$(OPENRAM_PATH)/miniconda
export OPENRAM_HOME=$(OPENRAM_PATH)/compiler
export OPENRAM_TECH=$(OPENRAM_PATH)/technology
export PYTHONPATH=$(OPENRAM_HOME)

.PHONY: all
all:
	python3 $(PWD)/test_sram_sus.py
	$(MAKE) $(OBJECTS)

%:
	source $(CONDA_HOME)/bin/activate ;\
	python3 $(OPENRAM_HOME)/../sram_compiler.py $(PWD)/config/$@.py
	sed -i -E 's/falling_edge/rising_edge/g' $(PWD)/output/$(basename $@)/$(basename $@)_TT_1p0V_25C.lib
	source $(CONDA_HOME)/bin/activate ;\
	python3 $(PWD)/area.py $(PWD)/output/$(basename $@)/$(basename $@).gds > $(PWD)/output/$(basename $@)/$(basename $@).area.txt
	cat ./output/$(basename $(notdir $@))/$(basename $(notdir $@)).area.txt | xargs -I {} sed -i -E 's/area : .*/area : {}/g' output/$(basename $(notdir $@))/$(basename $(notdir $@))_TT_1p0V_25C.lib
	cd $(PWD)/output/$(basename $@) ;\
	lc_shell -x 'read_lib $(PWD)/output/$(basename $@)/$(basename $@)_TT_1p0V_25C.lib; write_lib $(basename $@)_TT_1p0V_25C_lib; exit' ;\
	rm -f lc*.log lc*.txt

.PHONY: clean
clean:
	rm -rf output