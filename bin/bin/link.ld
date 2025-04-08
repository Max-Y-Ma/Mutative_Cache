OUTPUT_ARCH("riscv")
ENTRY(_start)

_text_start  = 0x60000000;
_sram_start = 0x70000000;
_stack_top  = 0x70001FFC;

/* Declare other memory mapped sections */


MEMORY
{
  FLASH(rx) : ORIGIN = _text_start, LENGTH = 16M
  SRAM(rw) : ORIGIN = _sram_start, LENGTH = 8K
}

SECTIONS
{
  /* Set location pointer to start of text section */
  . = _text_start; 

  /* Mark start of text section using location pointer */
  _text_start = .;

  /* Allocate start of text section to software initialization
   * - Initilize .bss section to all zeros
   * - Set stack pointer register (x2) to 
   */
  .text.swinit1 :
  {
    . = ALIGN(4);
    *(.text.swinit1)
  } > FLASH

  /* Main location for instruction */
  .text :
  {
    . = ALIGN(4);
    _text_vma_start = .;

    *(.text)

    . = ALIGN(4);
    _text_vma_end = .;
  } > FLASH

  /* Allocate end of text section for software finish, aka infinite loop */
  .text.swfin :
  {
    . = ALIGN(4);
    *(.text.swfin)
  } > FLASH

  /* Mark end of text section using location pointer */
  _text_end = .;

  /* Set location pointer to start of SRAM section */
  . = _sram_start;

  /* Uninitilized variables */
  .bss :
  {
    . = ALIGN(4);
    _bss_vma_start = .;

    *(.*bss*)

    . = ALIGN(4);
    _bss_vma_end = .;
  } > SRAM

  /* 
   * Mapped initialized variables for compatibility reasons 
   * Note: The programmer must manually initialize these varaibles to desired
   *       value, default initialization is not supported.
   */
  .data (NOLOAD) :
  {
    . = ALIGN(4);
    _data_vma_start = .;

    *(.*data*)

    . = ALIGN(4);
    _data_vma_end = .;
  } > SRAM

  /* Mapped initialized constant variables for compatibility reasons
   * Note: The programmer must manually initialize these varaibles to desired
   *       value, default initialization is not supported.
   */
  .rodata (NOLOAD) :
  {
    . = ALIGN(4);
    _rodata_vma_start = .;

    *(.*rodata*)

    . = ALIGN(4);
    _rodata_vma_end = .;
  } > SRAM

  /* Indicate start of heap section although unsupported */
  _heap_start = .;

  /* Indicate end of heap section although unsupported */
  _heap_end = .;

  /* Mark end of sram section using location pointer */
  _sram_end = .;

  /* Mark end of everything using location pointer */
  _end = .;

  /DISCARD/ :
  {
    *(.eh_frame)
    *(.riscv.attributes)
    *(.comment)
    *(.debug*)
  }
}
