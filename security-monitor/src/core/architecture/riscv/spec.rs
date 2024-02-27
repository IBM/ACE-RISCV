// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

// TODO: these constants should be generated from the spec
#![allow(unused)]
pub const CAUSE_INTERRUPT_BIT: usize = 63;

pub const CSR_FFLAGS: u16 = 0x1;
pub const CSR_FRM: u16 = 0x2;
pub const CSR_FCSR: u16 = 0x3;
pub const CSR_VSTART: u16 = 0x8;
pub const CSR_VXSAT: u16 = 0x9;
pub const CSR_VXRM: u16 = 0xa;
pub const CSR_VCSR: u16 = 0xf;
pub const CSR_SEED: u16 = 0x15;
pub const CSR_CYCLE: u16 = 0xc00;
pub const CSR_TIME: u16 = 0xc01;
pub const CSR_INSTRET: u16 = 0xc02;

pub const CSR_VL: u16 = 0xc20;
pub const CSR_VTYPE: u16 = 0xc21;
pub const CSR_VLENB: u16 = 0xc22;

pub const CSR_SSTATUS: u16 = 0x100;
pub const CSR_SEDELEG: u16 = 0x102;
pub const CSR_SIDELEG: u16 = 0x103;
pub const CSR_SIE: u16 = 0x104;
pub const CSR_STVEC: u16 = 0x105;
pub const CSR_SCOUNTEREN: u16 = 0x106;
pub const CSR_SENVCFG: u16 = 0x10a;
pub const CSR_SSCRATCH: u16 = 0x140;
pub const CSR_SEPC: u16 = 0x141;
pub const CSR_SCAUSE: u16 = 0x142;
pub const CSR_STVAL: u16 = 0x143;
pub const CSR_SIP: u16 = 0x144;
pub const CSR_STIMECMP: u16 = 0x14d;
pub const CSR_SISELECT: u16 = 0x150;
pub const CSR_SIREG: u16 = 0x151;
pub const CSR_STOPEI: u16 = 0x15c;
pub const CSR_SATP: u16 = 0x180;
pub const CSR_STOPI: u16 = 0xdb0;
pub const CSR_SCONTEXT: u16 = 0x5a8;
pub const CSR_VSSTATUS: u16 = 0x200;
pub const CSR_VSIE: u16 = 0x204;
pub const CSR_VSTVEC: u16 = 0x205;
pub const CSR_VSSCRATCH: u16 = 0x240;
pub const CSR_VSEPC: u16 = 0x241;
pub const CSR_VSCAUSE: u16 = 0x242;
pub const CSR_VSTVAL: u16 = 0x243;
pub const CSR_VSIP: u16 = 0x244;
pub const CSR_VSTIMECMP: u16 = 0x24d;
pub const CSR_VSISELECT: u16 = 0x250;
pub const CSR_VSIREG: u16 = 0x251;
pub const CSR_VSTOPEI: u16 = 0x25c;
pub const CSR_VSATP: u16 = 0x280;
pub const CSR_VSTOPI: u16 = 0xeb0;
pub const CSR_HSTATUS: u16 = 0x600;
pub const CSR_HEDELEG: u16 = 0x602;
pub const CSR_HIDELEG: u16 = 0x603;
pub const CSR_HIE: u16 = 0x604;
pub const CSR_HTIMEDELTA: u16 = 0x605;
pub const CSR_HCOUNTEREN: u16 = 0x606;
pub const CSR_HGEIE: u16 = 0x607;
pub const CSR_HVICTL: u16 = 0x609;
pub const CSR_HENVCFG: u16 = 0x60a;
pub const CSR_HTVAL: u16 = 0x643;
pub const CSR_HIP: u16 = 0x644;
pub const CSR_HVIP: u16 = 0x645;
pub const CSR_HTINST: u16 = 0x64a;
pub const CSR_HGATP: u16 = 0x680;
pub const CSR_HCONTEXT: u16 = 0x6a8;
pub const CSR_HGEIP: u16 = 0xe12;
pub const CSR_UTVT: u16 = 0x7;
pub const CSR_UNXTI: u16 = 0x45;
pub const CSR_UINTSTATUS: u16 = 0x46;
pub const CSR_USCRATCHCSW: u16 = 0x48;
pub const CSR_USCRATCHCSWL: u16 = 0x49;
pub const CSR_STVT: u16 = 0x107;
pub const CSR_SNXTI: u16 = 0x145;
pub const CSR_SINTSTATUS: u16 = 0x146;
pub const CSR_SSCRATCHCSW: u16 = 0x148;
pub const CSR_SSCRATCHCSWL: u16 = 0x149;
pub const CSR_MTVT: u16 = 0x307;
pub const CSR_MNXTI: u16 = 0x345;
pub const CSR_MINTSTATUS: u16 = 0x346;
pub const CSR_MSCRATCHCSW: u16 = 0x348;
pub const CSR_MSCRATCHCSWL: u16 = 0x349;
pub const CSR_MSTATUS: u16 = 0x300;
pub const CSR_MISA: u16 = 0x301;
pub const CSR_MEDELEG: u16 = 0x302;
pub const CSR_MIDELEG: u16 = 0x303;
pub const CSR_MIE: u16 = 0x304;
pub const CSR_MTVEC: u16 = 0x305;
pub const CSR_MCOUNTEREN: u16 = 0x306;
pub const CSR_MENVCFG: u16 = 0x30a;
pub const CSR_MCOUNTINHIBIT: u16 = 0x320;
pub const CSR_MSCRATCH: u16 = 0x340;
pub const CSR_MEPC: u16 = 0x341;
pub const CSR_MCAUSE: u16 = 0x342;
pub const CSR_MTVAL: u16 = 0x343;
pub const CSR_MIP: u16 = 0x344;
pub const CSR_MTINST: u16 = 0x34a;
pub const CSR_MTVAL2: u16 = 0x34b;
pub const CSR_PMPCFG0: u16 = 0x3a0;
pub const CSR_PMPCFG1: u16 = 0x3a1;
pub const CSR_PMPCFG2: u16 = 0x3a2;
pub const CSR_PMPCFG3: u16 = 0x3a3;
pub const CSR_PMPCFG4: u16 = 0x3a4;
pub const CSR_PMPCFG5: u16 = 0x3a5;
pub const CSR_PMPCFG6: u16 = 0x3a6;
pub const CSR_PMPCFG7: u16 = 0x3a7;
pub const CSR_PMPCFG8: u16 = 0x3a8;
pub const CSR_PMPCFG9: u16 = 0x3a9;
pub const CSR_PMPCFG10: u16 = 0x3aa;
pub const CSR_PMPCFG11: u16 = 0x3ab;
pub const CSR_PMPCFG12: u16 = 0x3ac;
pub const CSR_PMPCFG13: u16 = 0x3ad;
pub const CSR_PMPCFG14: u16 = 0x3ae;
pub const CSR_PMPCFG15: u16 = 0x3af;
pub const CSR_PMPADDR0: u16 = 0x3b0;
pub const CSR_PMPADDR1: u16 = 0x3b1;
pub const CSR_PMPADDR2: u16 = 0x3b2;
pub const CSR_PMPADDR3: u16 = 0x3b3;
pub const CSR_PMPADDR4: u16 = 0x3b4;
pub const CSR_PMPADDR5: u16 = 0x3b5;
pub const CSR_PMPADDR6: u16 = 0x3b6;
pub const CSR_PMPADDR7: u16 = 0x3b7;
pub const CSR_PMPADDR8: u16 = 0x3b8;
pub const CSR_PMPADDR9: u16 = 0x3b9;
pub const CSR_PMPADDR10: u16 = 0x3ba;
pub const CSR_PMPADDR11: u16 = 0x3bb;
pub const CSR_PMPADDR12: u16 = 0x3bc;
pub const CSR_PMPADDR13: u16 = 0x3bd;
pub const CSR_PMPADDR14: u16 = 0x3be;
pub const CSR_PMPADDR15: u16 = 0x3bf;
pub const CSR_PMPADDR16: u16 = 0x3c0;
pub const CSR_PMPADDR17: u16 = 0x3c1;
pub const CSR_PMPADDR18: u16 = 0x3c2;
pub const CSR_PMPADDR19: u16 = 0x3c3;
pub const CSR_PMPADDR20: u16 = 0x3c4;
pub const CSR_PMPADDR21: u16 = 0x3c5;
pub const CSR_PMPADDR22: u16 = 0x3c6;
pub const CSR_PMPADDR23: u16 = 0x3c7;
pub const CSR_PMPADDR24: u16 = 0x3c8;
pub const CSR_PMPADDR25: u16 = 0x3c9;
pub const CSR_PMPADDR26: u16 = 0x3ca;
pub const CSR_PMPADDR27: u16 = 0x3cb;
pub const CSR_PMPADDR28: u16 = 0x3cc;
pub const CSR_PMPADDR29: u16 = 0x3cd;
pub const CSR_PMPADDR30: u16 = 0x3ce;
pub const CSR_PMPADDR31: u16 = 0x3cf;
pub const CSR_PMPADDR32: u16 = 0x3d0;
pub const CSR_PMPADDR33: u16 = 0x3d1;
pub const CSR_PMPADDR34: u16 = 0x3d2;
pub const CSR_PMPADDR35: u16 = 0x3d3;
pub const CSR_PMPADDR36: u16 = 0x3d4;
pub const CSR_PMPADDR37: u16 = 0x3d5;
pub const CSR_PMPADDR38: u16 = 0x3d6;
pub const CSR_PMPADDR39: u16 = 0x3d7;
pub const CSR_PMPADDR40: u16 = 0x3d8;
pub const CSR_PMPADDR41: u16 = 0x3d9;
pub const CSR_PMPADDR42: u16 = 0x3da;
pub const CSR_PMPADDR43: u16 = 0x3db;
pub const CSR_PMPADDR44: u16 = 0x3dc;
pub const CSR_PMPADDR45: u16 = 0x3dd;
pub const CSR_PMPADDR46: u16 = 0x3de;
pub const CSR_PMPADDR47: u16 = 0x3df;
pub const CSR_PMPADDR48: u16 = 0x3e0;
pub const CSR_PMPADDR49: u16 = 0x3e1;
pub const CSR_PMPADDR50: u16 = 0x3e2;
pub const CSR_PMPADDR51: u16 = 0x3e3;
pub const CSR_PMPADDR52: u16 = 0x3e4;
pub const CSR_PMPADDR53: u16 = 0x3e5;
pub const CSR_PMPADDR54: u16 = 0x3e6;
pub const CSR_PMPADDR55: u16 = 0x3e7;
pub const CSR_PMPADDR56: u16 = 0x3e8;
pub const CSR_PMPADDR57: u16 = 0x3e9;
pub const CSR_PMPADDR58: u16 = 0x3ea;
pub const CSR_PMPADDR59: u16 = 0x3eb;
pub const CSR_PMPADDR60: u16 = 0x3ec;
pub const CSR_PMPADDR61: u16 = 0x3ed;
pub const CSR_PMPADDR62: u16 = 0x3ee;
pub const CSR_PMPADDR63: u16 = 0x3ef;
pub const CSR_MSECCFG: u16 = 0x747;
pub const CSR_TSELECT: u16 = 0x7a0;
pub const CSR_TDATA1: u16 = 0x7a1;
pub const CSR_TDATA2: u16 = 0x7a2;
pub const CSR_TDATA3: u16 = 0x7a3;
pub const CSR_TINFO: u16 = 0x7a4;
pub const CSR_TCONTROL: u16 = 0x7a5;
pub const CSR_MCONTEXT: u16 = 0x7a8;
pub const CSR_MSCONTEXT: u16 = 0x7aa;
pub const CSR_DCSR: u16 = 0x7b0;
pub const CSR_DPC: u16 = 0x7b1;
pub const CSR_DSCRATCH0: u16 = 0x7b2;
pub const CSR_DSCRATCH1: u16 = 0x7b3;
pub const CSR_MCYCLE: u16 = 0xb00;
pub const CSR_MINSTRET: u16 = 0xb02;
pub const CSR_MHPMCOUNTER3: u16 = 0xb03;
pub const CSR_MHPMCOUNTER4: u16 = 0xb04;
pub const CSR_MHPMCOUNTER5: u16 = 0xb05;
pub const CSR_MHPMCOUNTER6: u16 = 0xb06;
pub const CSR_MHPMCOUNTER7: u16 = 0xb07;
pub const CSR_MHPMCOUNTER8: u16 = 0xb08;
pub const CSR_MHPMCOUNTER9: u16 = 0xb09;
pub const CSR_MHPMCOUNTER10: u16 = 0xb0a;
pub const CSR_MHPMCOUNTER11: u16 = 0xb0b;
pub const CSR_MHPMCOUNTER12: u16 = 0xb0c;
pub const CSR_MHPMCOUNTER13: u16 = 0xb0d;
pub const CSR_MHPMCOUNTER14: u16 = 0xb0e;
pub const CSR_MHPMCOUNTER15: u16 = 0xb0f;
pub const CSR_MHPMCOUNTER16: u16 = 0xb10;
pub const CSR_MHPMCOUNTER17: u16 = 0xb11;
pub const CSR_MHPMCOUNTER18: u16 = 0xb12;
pub const CSR_MHPMCOUNTER19: u16 = 0xb13;
pub const CSR_MHPMCOUNTER20: u16 = 0xb14;
pub const CSR_MHPMCOUNTER21: u16 = 0xb15;
pub const CSR_MHPMCOUNTER22: u16 = 0xb16;
pub const CSR_MHPMCOUNTER23: u16 = 0xb17;
pub const CSR_MHPMCOUNTER24: u16 = 0xb18;
pub const CSR_MHPMCOUNTER25: u16 = 0xb19;
pub const CSR_MHPMCOUNTER26: u16 = 0xb1a;
pub const CSR_MHPMCOUNTER27: u16 = 0xb1b;
pub const CSR_MHPMCOUNTER28: u16 = 0xb1c;
pub const CSR_MHPMCOUNTER29: u16 = 0xb1d;
pub const CSR_MHPMCOUNTER30: u16 = 0xb1e;
pub const CSR_MHPMCOUNTER31: u16 = 0xb1f;
pub const CSR_MHPMEVENT3: u16 = 0x323;
pub const CSR_MHPMEVENT4: u16 = 0x324;
pub const CSR_MHPMEVENT5: u16 = 0x325;
pub const CSR_MHPMEVENT6: u16 = 0x326;
pub const CSR_MHPMEVENT7: u16 = 0x327;
pub const CSR_MHPMEVENT8: u16 = 0x328;
pub const CSR_MHPMEVENT9: u16 = 0x329;
pub const CSR_MHPMEVENT10: u16 = 0x32a;
pub const CSR_MHPMEVENT11: u16 = 0x32b;
pub const CSR_MHPMEVENT12: u16 = 0x32c;
pub const CSR_MHPMEVENT13: u16 = 0x32d;
pub const CSR_MHPMEVENT14: u16 = 0x32e;
pub const CSR_MHPMEVENT15: u16 = 0x32f;
pub const CSR_MHPMEVENT16: u16 = 0x330;
pub const CSR_MHPMEVENT17: u16 = 0x331;
pub const CSR_MHPMEVENT18: u16 = 0x332;
pub const CSR_MHPMEVENT19: u16 = 0x333;
pub const CSR_MHPMEVENT20: u16 = 0x334;
pub const CSR_MHPMEVENT21: u16 = 0x335;
pub const CSR_MHPMEVENT22: u16 = 0x336;
pub const CSR_MHPMEVENT23: u16 = 0x337;
pub const CSR_MHPMEVENT24: u16 = 0x338;
pub const CSR_MHPMEVENT25: u16 = 0x339;
pub const CSR_MHPMEVENT26: u16 = 0x33a;
pub const CSR_MHPMEVENT27: u16 = 0x33b;
pub const CSR_MHPMEVENT28: u16 = 0x33c;
pub const CSR_MHPMEVENT29: u16 = 0x33d;
pub const CSR_MHPMEVENT30: u16 = 0x33e;
pub const CSR_MHPMEVENT31: u16 = 0x33f;
pub const CSR_MVENDORID: u16 = 0xf11;
pub const CSR_MARCHID: u16 = 0xf12;
pub const CSR_MIMPID: u16 = 0xf13;
pub const CSR_MHARTID: u16 = 0xf14;
pub const CSR_MCONFIGPTR: u16 = 0xf15;
pub const CSR_HTIMEDELTAH: u16 = 0x615;
pub const CSR_HENVCFGH: u16 = 0x61a;
pub const CSR_CYCLEH: u16 = 0xc80;
pub const CSR_TIMEH: u16 = 0xc81;
pub const CSR_INSTRETH: u16 = 0xc82;
pub const CSR_HPMCOUNTER3H: u16 = 0xc83;
pub const CSR_HPMCOUNTER4H: u16 = 0xc84;
pub const CSR_HPMCOUNTER5H: u16 = 0xc85;
pub const CSR_HPMCOUNTER6H: u16 = 0xc86;
pub const CSR_HPMCOUNTER7H: u16 = 0xc87;
pub const CSR_HPMCOUNTER8H: u16 = 0xc88;
pub const CSR_HPMCOUNTER9H: u16 = 0xc89;
pub const CSR_HPMCOUNTER10H: u16 = 0xc8a;
pub const CSR_HPMCOUNTER11H: u16 = 0xc8b;
pub const CSR_HPMCOUNTER12H: u16 = 0xc8c;
pub const CSR_HPMCOUNTER13H: u16 = 0xc8d;
pub const CSR_HPMCOUNTER14H: u16 = 0xc8e;
pub const CSR_HPMCOUNTER15H: u16 = 0xc8f;
pub const CSR_HPMCOUNTER16H: u16 = 0xc90;
pub const CSR_HPMCOUNTER17H: u16 = 0xc91;
pub const CSR_HPMCOUNTER18H: u16 = 0xc92;
pub const CSR_HPMCOUNTER19H: u16 = 0xc93;
pub const CSR_HPMCOUNTER20H: u16 = 0xc94;
pub const CSR_HPMCOUNTER21H: u16 = 0xc95;
pub const CSR_HPMCOUNTER22H: u16 = 0xc96;
pub const CSR_HPMCOUNTER23H: u16 = 0xc97;
pub const CSR_HPMCOUNTER24H: u16 = 0xc98;
pub const CSR_HPMCOUNTER25H: u16 = 0xc99;
pub const CSR_HPMCOUNTER26H: u16 = 0xc9a;
pub const CSR_HPMCOUNTER27H: u16 = 0xc9b;
pub const CSR_HPMCOUNTER28H: u16 = 0xc9c;
pub const CSR_HPMCOUNTER29H: u16 = 0xc9d;
pub const CSR_HPMCOUNTER30H: u16 = 0xc9e;
pub const CSR_HPMCOUNTER31H: u16 = 0xc9f;
pub const CSR_MSTATUSH: u16 = 0x310;
pub const CSR_MENVCFGH: u16 = 0x31a;
pub const CSR_MSECCFGH: u16 = 0x757;
pub const CSR_MCYCLEH: u16 = 0xb80;
pub const CSR_MINSTRETH: u16 = 0xb82;
pub const CSR_MHPMCOUNTER3H: u16 = 0xb83;
pub const CSR_MHPMCOUNTER4H: u16 = 0xb84;
pub const CSR_MHPMCOUNTER5H: u16 = 0xb85;
pub const CSR_MHPMCOUNTER6H: u16 = 0xb86;
pub const CSR_MHPMCOUNTER7H: u16 = 0xb87;
pub const CSR_MHPMCOUNTER8H: u16 = 0xb88;
pub const CSR_MHPMCOUNTER9H: u16 = 0xb89;
pub const CSR_MHPMCOUNTER10H: u16 = 0xb8a;
pub const CSR_MHPMCOUNTER11H: u16 = 0xb8b;
pub const CSR_MHPMCOUNTER12H: u16 = 0xb8c;
pub const CSR_MHPMCOUNTER13H: u16 = 0xb8d;
pub const CSR_MHPMCOUNTER14H: u16 = 0xb8e;
pub const CSR_MHPMCOUNTER15H: u16 = 0xb8f;
pub const CSR_MHPMCOUNTER16H: u16 = 0xb90;
pub const CSR_MHPMCOUNTER17H: u16 = 0xb91;
pub const CSR_MHPMCOUNTER18H: u16 = 0xb92;
pub const CSR_MHPMCOUNTER19H: u16 = 0xb93;
pub const CSR_MHPMCOUNTER20H: u16 = 0xb94;
pub const CSR_MHPMCOUNTER21H: u16 = 0xb95;
pub const CSR_MHPMCOUNTER22H: u16 = 0xb96;
pub const CSR_MHPMCOUNTER23H: u16 = 0xb97;
pub const CSR_MHPMCOUNTER24H: u16 = 0xb98;
pub const CSR_MHPMCOUNTER25H: u16 = 0xb99;
pub const CSR_MHPMCOUNTER26H: u16 = 0xb9a;
pub const CSR_MHPMCOUNTER27H: u16 = 0xb9b;
pub const CSR_MHPMCOUNTER28H: u16 = 0xb9c;
pub const CSR_MHPMCOUNTER29H: u16 = 0xb9d;
pub const CSR_MHPMCOUNTER30H: u16 = 0xb9e;
pub const CSR_MHPMCOUNTER31H: u16 = 0xb9f;
pub const CAUSE_MISALIGNED_FETCH: u8 = 0x0;
pub const CAUSE_FETCH_ACCESS: u8 = 0x1;
pub const CAUSE_ILLEGAL_INSTRUCTION: u8 = 0x2;
pub const CAUSE_BREAKPOINT: u8 = 0x3;
pub const CAUSE_MISALIGNED_LOAD: u8 = 0x4;
pub const CAUSE_LOAD_ACCESS: u8 = 0x5;
pub const CAUSE_MISALIGNED_STORE: u8 = 0x6;
pub const CAUSE_STORE_ACCESS: u8 = 0x7;
pub const CAUSE_USER_ECALL: u8 = 0x8;
pub const CAUSE_SUPERVISOR_ECALL: u8 = 0x9;
pub const CAUSE_VIRTUAL_SUPERVISOR_ECALL: u8 = 0xa;
pub const CAUSE_MACHINE_ECALL: u8 = 0xb;
pub const CAUSE_FETCH_PAGE_FAULT: u8 = 0xc;
pub const CAUSE_LOAD_PAGE_FAULT: u8 = 0xd;
pub const CAUSE_STORE_PAGE_FAULT: u8 = 0xf;
pub const CAUSE_FETCH_GUEST_PAGE_FAULT: u8 = 0x14;
pub const CAUSE_LOAD_GUEST_PAGE_FAULT: u8 = 0x15;
pub const CAUSE_VIRTUAL_INSTRUCTION: u8 = 0x16;
pub const CAUSE_STORE_GUEST_PAGE_FAULT: u8 = 0x17;

pub const CSR_HSTATUS_SPV: usize = 7;
pub const CSR_HSTATUS_GVA: usize = 6;

pub const CSR_MSTATUS_SIE: usize = 1;
pub const CSR_MSTATUS_MIE: usize = 3;
pub const CSR_MSTATUS_MPIE: usize = 7;
pub const CSR_MSTATUS_SPP: usize = 8;
pub const CSR_MSTATUS_MPP: usize = 11;
pub const CSR_MSTATUS_GVA: usize = 38;
pub const CSR_MSTATUS_MPV: usize = 39;
pub const CSR_MSTATUS_MPRV: usize = 17;

pub const MIE_MSIP: usize = 3;
pub const MIE_MSIP_MASK: usize = 1 << MIE_MSIP;
pub const MIE_MTIP: usize = 7;
pub const MIE_MTIP_MASK: usize = 1 << MIE_MTIP;
pub const MIE_MEIP: usize = 11;
pub const MIE_MEIP_MASK: usize = 1 << MIE_MEIP;
pub const MIE_SSIP: usize = 1;
pub const MIE_SSIP_MASK: usize = 1 << MIE_SSIP;
pub const MIE_STIP: usize = 5;
pub const MIE_STIP_MASK: usize = 1 << MIE_STIP;
pub const MIE_SEIP: usize = 9;
pub const MIE_SEIP_MASK: usize = 1 << MIE_SEIP;

pub const PMP_OFF_MASK: usize = 0b0;
pub const PMP_TOR_MASK: usize = 0b01000;
pub const PMP_NA4_MASK: usize = 0b10000;
pub const PMP_NAPOT_MASK: usize = 0b11000;
pub const PMP_PERMISSION_NONE_MASK: usize = 0;
pub const PMP_PERMISSION_RWX_MASK: usize = 0b111;
pub const PMP_CONFIG_SHIFT: usize = 8;
pub const PMP_ADDRESS_SHIFT: u16 = 2;

pub const MTVEC_BASE_SHIFT: usize = 2;

pub const CSR_STATUS_SIE: usize = 1;
