# Memory Sections
- NAME, START_ADDRESS, LENGTH
- FLASH, 0x60000000, 16MB
- SRAM, 0x70000000, 8KB

# Linker Sections
## SRAM
- .bss (0x70000000)
- .data
- .rodata
- .heap
- .stack (0x70001000)

## FLASH
  - .text (0x60000000)
  - .text_end (0x60800000)

# Details
- Acadia support a Harvard architecture and does not read from instruction
memory (FLASH). As a result, we cannot have a .data section for initialized 
variables or a .rodata section for initialized constants. All static variables
must be in the .bss section, which is uninitalized and in SRAM. The .data and
.rodata sections are mapped here for compatibility reasons but do not contain
the initialized values.
- With the memory sections in mind, the programmer is responsible for loading
the correct initialized values using explicit instructions. In the RV32IMC
architecture supported by Acadia, these can be done simply by using the 
LUI and ADDI instruction. Additionally, the C compiler should generate these
instructions from assignments.
- The .heap section starts after the .bss, .data, and .rodata sections. Dynamic
memory will be placed here and runs until the end of the SRAM, which is the
location for the start of the .stack section. These sections behave as the
normal concepts of heap and stack. Currently, there is no library support
for dynamic memory allocation functions like malloc() and free().