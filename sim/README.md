# Simulation Instructions

## Simulate core running a c/asm program
Generate binaries for simulation. Program can be .c, or .s file. Outputs .elf to ```bin/<progname>.elf``` and .lst flash image to ```sim/memory_flash.lst```.
>```make compile SPIKE=1 PROG=<Path to program>```

Run .elf through RISC-V Golden model, creates trace file ```sim/spike.log```
>```make spike ELF=<path to elf>```

Run .elf through our processor. memory_flash.lst is loaded into flash model, design is reset, then run. Ouputs trace file to ```sim/commit.log```. Will output sim failed due to some warnings. Sim actually fails when you see RVFI error or spike mismatches (next step).
>```make vc DIR=soc```

Check if core trace matches golden model.
>```diff -s sim/commit.log sim/spike.log```

View simulation trace using verdi
>```make verdi```

Example test (run in ```<repo>/digital/sim```)
```
make clean
make compile SPIKE=1 PROG=../chip/testcode/soc/src/soc.s
make spike ELF=bin/soc.elf
make vc DIR=soc
diff -s sim/commit.log sim/spike.log
```