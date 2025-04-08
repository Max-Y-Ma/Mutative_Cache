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
  slti x0, x0, -256
  call _fini

.section ".text.swfin"
.globl _fini
_fini:
    beq x0, x0, _fini
    .rept 256
    nop
    .endr

.section ".tohost"
.globl tohost
tohost: .dword 0
.section ".fromhost"
.globl fromhost
fromhost: .dword 0
