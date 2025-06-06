#!/bin/bash

# Settings
# Available options are rv32i, rv32ic, rv32im, rv32imc
ARCH=rv32imc
# Bytes per memory address. Note that you may need to change this as your memory model evolves throughout the MP
# or you use memories from past MPs for testing purposes.
#   Magic Memory = 32 bits per address -> 4 byte ADDRESSABILITY
#   Burst Memory = 64 bits per address -> 8 byte ADDRESSABILITY
#   Simple Memory = 256 bits per address -> 32 byte ADDRESSABILITY
#   Banked Memory = 256 bits per address -> 32 byte ADDRESSABILITY
ADDRESSABILITY=32

# some other settings
SH_LOCATION=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
WORK_DIR=$SH_LOCATION/../sim/bin
TARGET_DIR=$SH_LOCATION/../sim/sim
ASSEMBLER=$SH_LOCATION/tools/bin/riscv32-unknown-elf-gcc
OBJCOPY=$SH_LOCATION/tools/bin/riscv32-unknown-elf-objcopy
OBJDUMP=$SH_LOCATION/tools/bin/riscv32-unknown-elf-objdump
LINK_FILE=$SH_LOCATION/link.ld
START_FILE=$SH_LOCATION/startup.s
MEM_LST_START_ADDR="0x60000000" # in bytes

echo $SH_LOCATION

# Command line parameters
IN_FILE=$1

# Color for echo
RED='\033[0;31m'
ORG='\033[0;33m'
NC='\033[0m'

# Print usage
if [[ "$#" -lt 1 ]]; then
    echo -e "${RED}[ERROR]${NC} No source or ELF file provided."
    echo -e "[INFO]  Compile a C source file or RISC-V assembly file, or convert a RISC-V ELF file, into a memory file for simulation."
    echo -e "[INFO]  Usage: $0 <asm/src/elf file>"
    exit 1
fi

mkdir -p "$WORK_DIR"
mkdir -p "$TARGET_DIR"

# Copy files to temporary directory
cp "$IN_FILE" "$WORK_DIR"

function ecompile {
    ELF_FILE="${WORK_DIR}/$(basename "${IN_FILE%.*}").elf"
    rm -f $ELF_FILE
    "$ASSEMBLER" -mcmodel=medany -static -fno-common -ffreestanding -nostartfiles -march=$ARCH -mabi=ilp32 -Ofast -flto -Wall -Wextra -Wno-unused -T$LINK_FILE $START_FILE "${WORK_DIR}/$(basename $IN_FILE)" -o "$ELF_FILE" -lm -static-libgcc -lgcc -lc -Wl,--no-relax
    # Fail if object file doesn't exist or has no memory content
    if [[ ! -e "$ELF_FILE" || "$(cat "$ELF_FILE" | wc -c)" -le "1" ]]; then
        echo -e "${RED}[ERROR]${NC} Error assembling $IN_FILE, not generating binary file" >&2
        exit 2
    fi
    echo -e "[INFO]  Assembled/Compiled $IN_FILE to $ELF_FILE"
}

function edisassembly {
    DIS_FILE="${WORK_DIR}/$(basename "${ELF_FILE%.*}").dis"
    rm -f $DIS_FILE
    "$OBJDUMP" -D "$ELF_FILE" -Mnumeric > "$DIS_FILE"
}

function eobjcopy {
    BIN_FILE="${WORK_DIR}/$(basename "${ELF_FILE%.*}").bin"
    rm -f $BIN_FILE
    "$OBJCOPY" -O binary "$ELF_FILE" "$BIN_FILE"
    # Fail if binary file doesn't exist or has no memory content
    if [[ ! -e "$BIN_FILE" || "$(cat "$BIN_FILE" | wc -c)" -le "1" ]]; then
        echo -e "${RED}[ERROR]${NC} Error binarizing $ELF_FILE, not generating memory file >&2"
        exit 3
    fi
}

function log2 {
    local x=0
    for (( y=$1-1 ; $y > 0; y >>= 1 )) ; do
        let x=$x+1
    done
    echo $x
}

function egenerate {
    # Fail if the target directory doesn't exist
    if [[ ! -d "$(dirname "$1")" ]]; then
        echo -e "${RED}[ERROR]${NC} Directory $(dirname "$1") does not exist. >&2"
        exit 4
    fi

    if [ -e "$1" ]; then
        echo -e "${ORG}[WARN]${NC}  Target file $1 exists. Overwriting."
        rm "$1"
    fi

    # Write memory to file
    z=$( log2 $2 )
    result=$(( $3 >> $z ))
    mem_start=$(printf "@%08x\n" $result)

    {
        echo $mem_start
        hexdump -ve $2'/1 "%02X " "\n"' "$BIN_FILE" \
            | awk '{for (i = NF; i > 0; i--) printf "%s", $i; print ""}'
    } > "$1"

    echo -e "[INFO]  Wrote memory contents to $1"
}

# Testing if assembly file
if [ x"${IN_FILE##*.}" == "xs" ] || [ x"${IN_FILE##*.}" == "xasm" ]
then
    START_FILE=""
fi

# Testing if elf file
if [ x"${IN_FILE##*.}" == "xelf" ]
then
    ELF_FILE=$IN_FILE
else
    ecompile
fi

edisassembly
eobjcopy

for addressability in 1 4 8 32; do
    egenerate $TARGET_DIR/memory_$addressability.lst $addressability MEM_LST_START_ADDR
done

egenerate $TARGET_DIR/memory_flash.lst 1 0