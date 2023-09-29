OUTPUT_ARCH( "riscv" )
ENTRY( _start )

MEMORY {
  ram  (wxa) : ORIGIN = 0x80000000, LENGTH = 128M
}

PHDRS {
  text PT_LOAD;
  data PT_LOAD;
  bss PT_LOAD;
}

SECTIONS {
  .text : {
    PROVIDE(_text_start = .);
    *(.text.init) *(.text .text.*)
    PROVIDE(_text_end = .);
  } >ram AT>ram :text  

  .rodata : {
    PROVIDE(_rodata_start = .);
    *(.rodata .rodata.*)
    PROVIDE(_rodata_end = .);
  } >ram AT>ram :text

  .data : {
    . = ALIGN(4096);
    PROVIDE(_data_start = .);
     *(.data .data.*)

    . = ALIGN(8);
    PROVIDE(_global_pointer = . + 0x800);

    *(.sdata .sdata.*)
    PROVIDE(_data_end = .);
  } >ram AT>ram :data

  .bss : {
    . = ALIGN(8);
    PROVIDE(_bss_start = .);
    *(.sbss .sbss.*) *(.bss .bss.*)
    . = ALIGN(8);
    PROVIDE(_bss_end = .);
  } >ram AT>ram :bss

  PROVIDE(_memory_start = ORIGIN(ram));
  PROVIDE(_stack_start = _bss_end);
  PROVIDE(_stack_end = _stack_start + 0x100000); 
  PROVIDE(_memory_end = ORIGIN(ram) + LENGTH(ram));

  . = ALIGN(4096);
  PROVIDE(_dma_start = _stack_end + 0x10000); 
  PROVIDE(_dma_end = _dma_start + 0x100000); 

  . = ALIGN(4096);
  PROVIDE(_heap_start = _dma_end);
  PROVIDE(_heap_size = _memory_end - _heap_start);
}