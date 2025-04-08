.section ".text.swinit1"
.globl _start
_start:
_initbss:
  la t1, _bss_vma_start
  la t2, _rodata_vma_end
  beq t1, t2, _setup
_initbss_loop:
  sw x0, 0(t1)
  addi t1, t1, 4
  bltu t1, t2, _initbss_loop

_setup:
  la sp, _stack_top
  add s0, sp, x0
  call main
  call _fini

.section ".text.swfin"
.globl _fini
_fini:
  beq x0, x0, _fini
  .rept 16
  .word 0xECEB
  .endr
