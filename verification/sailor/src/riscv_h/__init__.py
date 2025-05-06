# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# -------------------------- This module scans the Sail model of RISC-V for instruction and function defintions ---------------------------------------- #
# -------- It then extracts the names of all the instructions and functions, for later use by Sailor (SailScanner) through the sail_syntax pkg --------- #
# ------------------------------- This module also scans the Sail model of RISC-V for CSR bitfield defintions ------------------------------------------ #
# -------- Not all CSRs have bitfields. For the CSRs that do, this code extracts the bitfields and adds them to the csr_list (for use by Sailor) ------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #

import os;
import csv;
from plex import *;
from sail_syntax import *;
from riscv.riscv_lexer import RISCV_Sail_Scanner, instruction_executable;

sail_model_dir = "";
results_dir = "";

SUPPORTED_MODES = ["U", "VU", "HS", "VS", "M"];

# --------------------------------- These are extracted from the RISC-V ISA specification implementation in Sail ---------------------------------------- #

function_names = [];
instruction_names = [];
files_to_scan_for_func_defs = [];
files_to_scan_for_instr_defs = [];

#augmented_function_names = ['step', ];
#files_to_scan_for_aug_func_defs = ['../../sail-riscv/model/riscv_step.sail', ];

# TODO: Functions to ignore should be computed dynamically. 
# functions_to_ignore = [];

initial_ctrl_reg_names = ['pmpaddr', 'pmpcfg'];

ctrl_reg_names = [];

# TODO: These should be extracted automatically.
functions_to_ignore = ['riscv_f16MulAdd', 'negate_H', 'canonical_NaN_H', 'riscv_f16Eq', 'riscv_f16Lt', 'riscv_f16Le', 'riscv_f16ToI32', 'riscv_f16ToUi32', 'riscv_i32ToF16', 'riscv_ui32ToF16', 'riscv_f32ToF16', 'riscv_f64ToF16', 'riscv_f16ToF32', 'riscv_f16ToF64', 'riscv_f16ToI64', 'riscv_f16ToUi64', 'riscv_i64ToF16', 'riscv_ui64ToF16', "to_num", "to_vec", "extern_ui64ToF16","extern_i64ToF16","print_insn","num_of_ExceptionType","Ext_DataAddr_OK","pc_alignment_mask","privLevel_to_bits","throw","Error_not_implemented","write_kind_of_flags", "write_ram_ea","mem_write_value_meta","if","vector","ones","to_bits","int_power","valid_segment","valid_vtype","valid_eew_emul","get_scalar","BitStr", "truncate", "slice", "mem_read","write_single_element","signed","Read","Write","match","sail_barrier","get_vtype_vta","__ReadRAM_Meta","Some", "to_str", "MemoryOpResult","MemoryOpResult_add_meta", "MemoryOpResult_drop_meta", "MemException", "MemValue","get_arch_pc", "X", "handle_illegal", "None", "option", "size_bytes", "sizeof", "sign_extend", "zero_extend", "internal_error", "shift_right_arith32", "shift_right_arith64", "assert", "bits", "check_misaligned", "bit_to_bool", "bool_to_bits", "not", "set_next_pc", "get_next_pc","string_take","string_drop","valid_hex_bits","V","zeros","unsigned","ext_check_xret_priv","ext_fail_xret_priv",'xt2', 'xt3', 'gfmul','isla_footprint_no_init', 'isla_footprint','writeCSR','init_platform', 'ext_init', 'init_sys', 'init_model', 'init_vregs', 'init_base_regs', 'init_masked_result', 'init_masked_source', 'init_masked_result_carry', 'init_masked_result_cmp', 'init_vmem', 'ext_init_regs', 'ext_rvfi_init', 'init_pmp', 'init_TLB', 'init_fdext_regs', 'ext_init','isCSRdefined','main', 'is_CSR_defined', 'rX', 'rV', 'rF'];

# TODO: Generate this dynamically too. 
# all_function_names = Str('xt2', 'xt3', 'gfmul', 'aes_mixcolumn_byte_fwd', 'aes_mixcolumn_byte_inv', 'aes_mixcolumn_fwd', 'aes_mixcolumn_inv', 'aes_decode_rcon', 'sbox_lookup', 'aes_sbox_fwd', 'aes_sbox_inv', 'aes_subword_fwd', 'aes_subword_inv', 'sm4_sbox', 'aes_get_column', 'aes_apply_fwd_sbox_to_each_byte', 'aes_apply_inv_sbox_to_each_byte', 'getbyte', 'aes_rv64_shiftrows_fwd', 'aes_rv64_shiftrows_inv', 'aes_shift_rows_fwd', 'aes_shift_rows_inv', 'aes_subbytes_fwd', 'aes_subbytes_inv', 'aes_mixcolumns_fwd', 'aes_mixcolumns_inv', 'csr_name', 'extend_value', 'is_aligned', 'effective_fence_set', 'compressed_measure', 'process_vlseg', 'process_vlsegff', 'process_vsseg', 'process_vlsseg', 'process_vssseg', 'process_vlxseg', 'process_vsxseg', 'process_vlre', 'process_vsre', 'process_vm', 'hex_bits_signed_forwards', 'hex_bits_signed_forwards_matches', 'parse_hex_bits_signed', 'valid_hex_bits_signed', 'hex_bits_signed_backwards', 'hex_bits_signed_backwards_matches', 'plat_htif_tohost', 'phys_mem_segments', 'within_phys_mem', 'within_clint', 'within_htif_writable', 'within_htif_readable', 'clint_load', 'clint_dispatch', 'clint_store', 'tick_clock', 'reset_htif', 'htif_load', 'htif_store', 'htif_tick', 'within_mmio_readable', 'within_mmio_readable', 'within_mmio_writable', 'within_mmio_writable', 'mmio_read', 'mmio_write', 'init_platform', 'tick_platform', 'platform_wfi', 'accessType_to_str', 'riscv_f16Add', 'riscv_f16Sub', 'riscv_f16Mul', 'riscv_f16Div', 'riscv_f32Add', 'riscv_f32Sub', 'riscv_f32Mul', 'riscv_f32Div', 'riscv_f64Add', 'riscv_f64Sub', 'riscv_f64Mul', 'riscv_f64Div', 'riscv_f16MulAdd', 'riscv_f32MulAdd', 'riscv_f64MulAdd', 'riscv_f16Sqrt', 'riscv_f32Sqrt', 'riscv_f64Sqrt', 'riscv_f16ToI32', 'riscv_f16ToUi32', 'riscv_i32ToF16', 'riscv_ui32ToF16', 'riscv_f16ToI64', 'riscv_f16ToUi64', 'riscv_i64ToF16', 'riscv_ui64ToF16', 'riscv_f32ToI32', 'riscv_f32ToUi32', 'riscv_i32ToF32', 'riscv_ui32ToF32', 'riscv_f32ToI64', 'riscv_f32ToUi64', 'riscv_i64ToF32', 'riscv_ui64ToF32', 'riscv_f64ToI32', 'riscv_f64ToUi32', 'riscv_i32ToF64', 'riscv_ui32ToF64', 'riscv_f64ToI64', 'riscv_f64ToUi64', 'riscv_i64ToF64', 'riscv_ui64ToF64', 'riscv_f16ToF32', 'riscv_f16ToF64', 'riscv_f32ToF64', 'riscv_f32ToF16', 'riscv_f64ToF16', 'riscv_f64ToF32', 'riscv_f16Lt', 'riscv_f16Lt_quiet', 'riscv_f16Le', 'riscv_f16Le_quiet', 'riscv_f16Eq', 'riscv_f32Lt', 'riscv_f32Lt_quiet', 'riscv_f32Le', 'riscv_f32Le_quiet', 'riscv_f32Eq', 'riscv_f64Lt', 'riscv_f64Lt_quiet', 'riscv_f64Le', 'riscv_f64Le_quiet', 'riscv_f64Eq', 'riscv_f16roundToInt', 'riscv_f32roundToInt', 'riscv_f64roundToInt', 'tick_pc', 'ext_veto_disable_C', 'write_ram', 'read_ram', 'can', 'undefined_SV_Params', 'fsplit_H', 'fmake_H', 'negate_H', 'fle_H', 'haveHalfFPU', 'ext_fetch_check_pc', 'ext_handle_fetch_check_error', 'ext_control_check_addr', 'ext_control_check_pc', 'ext_handle_control_check_error', 'ext_data_get_addr', 'ext_handle_data_check_error', 'ext_check_phys_mem_read', 'ext_check_phys_mem_write', 'ext_init', 'ext_fetch_hook', 'ext_pre_step_hook', 'ext_post_step_hook', 'csrAccess', 'csrPriv', 'is_CSR_defined', 'check_CSR_access', 'check_TVM_SATP', 'check_Counteren', 'check_seed_CSR', 'check_CSR', 'exception_delegatee', 'findPendingInterrupt', 'processPending', 'getPendingSet', 'dispatchInterrupt', 'tval', 'rvfi_trap', 'rvfi_trap', 'trap_handler', 'exception_handler', 'handle_mem_exception', 'handle_exception', 'handle_interrupt', 'init_sys', 'msbs_of_PTE', 'PPNs_of_PTE', 'pte_is_ptr', 'pte_is_invalid', 'check_PTE_permission', 'update_PTE_Bits', 'step', 'loop', 'init_model', 'lower_sstatus', 'lift_ustatus', 'legalize_ustatus', 'lower_sip', 'lower_sie', 'lift_uip', 'legalize_uip', 'lift_uie', 'legalize_uie', 'not_bit', 'bit_str', 'get_config_print_instr', 'get_config_print_reg', 'get_config_print_mem', 'get_config_print_platform', 'zeros_implicit', 'operator', 'operator', 'operator', 'operator', 'operator', 'operator', 'operator', 'operator', 'rotate_bits_right', 'rotate_bits_left', 'rotater', 'rotatel', 'reverse_bits_in_byte', 'log2', 'isRVC', 'fetch', 'writeCSR', 'dirty_v_context', 'dirty_v_context_if_present', 'rV', 'wV', 'rV_bits', 'wV_bits', 'init_vregs', 'ext_write_vcsr', 'get_num_elem', 'read_single_vreg', 'write_single_vreg', 'read_vreg', 'read_single_element', 'write_vreg', 'read_vmask', 'read_vmask_carry', 'write_vmask', 'valid_rounding_mode', 'nxFlag', 'ufFlag', 'ofFlag', 'dzFlag', 'nvFlag', 'fsplit_S', 'fmake_S', 'negate_S', 'feq_quiet_S', 'flt_S', 'fle_S', 'haveSingleFPU', 'process_fload64', 'process_fload32', 'process_fload16', 'process_fstore', 'process_rfvv_single', 'process_rfvv_widen', 'ext_decode_compressed', 'ext_decode', 'hex_bits_forwards', 'hex_bits_forwards_matches', 'hex_bits_backwards', 'hex_bits_backwards_matches', 'rX', 'rvfi_wX', 'rvfi_wX', 'wX', 'rX_bits', 'wX_bits', 'init_base_regs', 'assert_vstart', 'valid_fp_op', 'valid_rd_mask', 'valid_reg_overlap', 'illegal_normal', 'illegal_vd_masked', 'illegal_vd_unmasked', 'illegal_variable_width', 'illegal_reduction', 'illegal_reduction_widen', 'illegal_fp_normal', 'illegal_fp_vd_masked', 'illegal_fp_vd_unmasked', 'illegal_fp_variable_width', 'illegal_fp_reduction', 'illegal_fp_reduction_widen', 'illegal_load', 'illegal_store', 'illegal_indexed_load', 'illegal_indexed_store', 'get_start_element', 'get_end_element', 'init_masked_result', 'can', 'init_masked_source', 'init_masked_result_carry', 'init_masked_result_cmp', 'read_vreg_seg', 'canonical_NaN', 'f_is_neg_inf', 'f_is_neg_norm', 'f_is_neg_subnorm', 'f_is_neg_zero', 'f_is_pos_zero', 'f_is_pos_subnorm', 'f_is_pos_norm', 'f_is_pos_inf', 'f_is_SNaN', 'f_is_QNaN', 'f_is_NaN', 'get_scalar_fp', 'get_shift_amount', 'get_fixed_rounding_incr', 'unsigned_saturation', 'signed_saturation', 'get_fp_rounding_mode', 'negate_fp', 'fp_add', 'fp_sub', 'fp_min', 'fp_max', 'fp_eq', 'fp_gt', 'fp_ge', 'fp_lt', 'fp_le', 'fp_mul', 'fp_div', 'fp_muladd', 'fp_nmuladd', 'fp_mulsub', 'fp_nmulsub', 'fp_class', 'fp_widen', 'riscv_f16ToI16', 'riscv_f16ToI8', 'riscv_f32ToI16', 'riscv_f16ToUi16', 'riscv_f16ToUi8', 'riscv_f32ToUi16', 'count_leadingzeros', 'rsqrt7', 'riscv_f16Rsqrte7', 'riscv_f32Rsqrte7', 'riscv_f64Rsqrte7', 'recip7', 'riscv_f16Recip7', 'riscv_f32Recip7', 'riscv_f64Recip7', 'fsplit_D', 'fmake_D', 'negate_D', 'feq_quiet_D', 'flt_D', 'fle_D', 'haveDoubleFPU', 'validDoubleRegs', 'aqrl_str', 'lrsc_width_str', 'amo_width_valid', 'legalize_misa', 'haveAtomics', 'haveRVC', 'haveMulDiv', 'haveSupMode', 'haveUsrMode', 'haveNExt', 'haveZba', 'haveZbb', 'haveZbc', 'haveZbs', 'haveZfa', 'haveZbkb', 'haveZbkc', 'haveZbkx', 'haveZkr', 'haveZksh', 'haveZksed', 'haveZknh', 'haveZkne', 'haveZknd', 'haveZmmul', 'haveZaamo', 'haveZalrsc', 'haveZicond', 'lowest_supported_privLevel', 'have_privLevel', 'effectivePrivilege', 'get_mstatus_SXL', 'set_mstatus_SXL', 'get_mstatus_UXL', 'set_mstatus_UXL', 'legalize_mstatus', 'cur_Architecture', 'in32BitMode', 'haveFExt', 'haveDExt', 'haveZfh', 'haveVExt', 'haveSvinval', 'haveZcb', 'haveZhinx', 'haveZfinx', 'haveZdinx', 'legalize_mip', 'legalize_mie', 'legalize_mideleg', 'legalize_medeleg', 'legalize_tvec', 'tvec_addr', 'legalize_xepc', 'legalize_mcounteren', 'legalize_scounteren', 'legalize_mcountinhibit', 'retire_instruction', 'get_sstatus_UXL', 'set_sstatus_UXL', 'lower_mstatus', 'lift_sstatus', 'legalize_sstatus', 'legalize_sedeleg', 'lower_mip', 'lower_mie', 'lift_sip', 'legalize_sip', 'lift_sie', 'legalize_sie', 'legalize_satp64', 'legalize_satp32', 'read_seed_csr', 'write_seed_csr', 'legalize_menvcfg', 'legalize_senvcfg', 'is_fiom_active', 'get_sew_pow', 'get_sew', 'get_sew_bytes', 'get_lmul_pow', 'decode_agtype', 'get_vtype_vma', '__WriteRAM_Meta', 'regidx_to_regno', 'creg2reg_idx', 'architecture', 'arch_to_bits', 'not_implemented', 'privLevel_of_bits', 'privLevel_to_str', 'interruptType_to_bits', 'exceptionType_to_bits', 'exceptionType_to_str', 'trapVectorMode_of_bits', 'extStatus_to_bits', 'extStatus_of_bits', 'satp64Mode_of_bits', 'report_invalid_width', 'get_entry_point', 'get_entry_point', 'main', 'vpns_of_va', 'vpn_j_of_va', 'offset_of_va', 'is_valid_vAddr', 'pt_walk', 'legalize_satp', 'satp_to_asid', 'satp_to_PT_base', 'translationMode', 'write_pte', 'translate_TLB_hit', 'translate_TLB_miss', 'translate', 'translateAddr', 'init_vmem', 'FRegStr', 'fregval_from_freg', 'fregval_into_freg', 'ext_init_regs', 'ext_rvfi_init', 'ext_check_CSR', 'ext_check_CSR_fail', 'is_aligned_addr', 'read_kind_of_flags', 'phys_mem_read', 'phys_access_check', 'checked_mem_read', 'rvfi_read', 'rvfi_read', 'mem_read_priv_meta', 'mem_read_meta', 'mem_read_priv', 'mem_write_ea', 'rvfi_write', 'rvfi_write', 'phys_mem_write', 'checked_mem_write', 'mem_write_value_priv_meta', 'mem_write_value_priv', 'mem_write_value', 'pmpAddrRange', 'pmpCheckRWX', 'pmpCheckPerms', 'pmpMatchAddr', 'pmpMatchEntry', 'accessToFault', 'pmpCheck', 'init_pmp', 'get_elen_pow', 'get_vlen_pow', 'spc_forwards', 'spc_forwards_matches', 'spc_backwards', 'opt_spc_forwards', 'opt_spc_forwards_matches', 'opt_spc_backwards', 'opt_spc_backwards_matches', 'def_spc_forwards', 'def_spc_forwards_matches', 'def_spc_backwards', 'def_spc_backwards_matches', 'nk_check_reg_access_privs', 'pmpAddrMatchType_of_bits', 'pmpAddrMatchType_to_bits', 'pmpReadCfgReg', 'pmpReadAddrReg', 'pmpLocked', 'pmpTORLocked', 'pmpWriteCfg', 'pmpWriteCfgReg', 'pmpWriteAddr', 'pmpWriteAddrReg', 'fetch', 'handle_trap_extension', 'prepare_trap_vector', 'get_xret_target', 'set_xret_target', 'prepare_xret_target', 'get_mtvec', 'get_stvec', 'get_utvec', 'set_mtvec', 'set_stvec', 'set_utvec', 'fcvtmod_helper', 'handle_illegal_vtype', 'calculate_new_vl', 'init_TLB', 'write_TLB', 'match_TLB_Entry', 'flush_TLB_Entry', 'lookup_TLB', 'add_to_TLB', 'flush_TLB', 'RegStr', 'regval_from_reg', 'regval_into_reg', 'ptw_error_to_str', 'ext_get_ptw_error', 'translationException', 'canonical_NaN_H', 'canonical_NaN_S', 'canonical_NaN_D', 'dirty_fd_context', 'dirty_fd_context_if_present', 'rF', 'wF', 'rF_bits', 'wF_bits', 'rF_H', 'wF_H', 'rF_S', 'wF_S', 'rF_D', 'wF_D', 'rF_or_X_H', 'rF_or_X_S', 'rF_or_X_D', 'wF_or_X_H', 'wF_or_X_S', 'wF_or_X_D', 'init_fdext_regs', 'ext_write_fcsr', 'accrue_fflags', 'rvfi_set_instr_packet', 'rvfi_get_cmd', 'rvfi_get_insn', 'print_instr_packet', 'rvfi_zero_exec_packet', 'rvfi_halt_exec_packet', 'rvfi_get_v2_support_packet', 'rvfi_get_exec_packet_v1', 'rvfi_get_v2_trace_size', 'rvfi_get_exec_packet_v2', 'rvfi_get_int_data', 'rvfi_get_mem_data', 'rvfi_encode_width_mask', 'print_rvfi_exec', 'ext_fetch_hook', 'ext_pre_step_hook', 'ext_post_step_hook', 'ext_init', 'ext_translate_exception', 'ext_exc_type_to_bits', 'num_of_ext_exc_type', 'ext_exc_type_to_str', 'riscv_f16MulAdd', 'negate_H', 'canonical_NaN_H', 'riscv_f16Eq', 'riscv_f16Lt', 'riscv_f16Le', 'riscv_f16ToI32', 'riscv_f16ToUi32', 'riscv_i32ToF16', 'riscv_ui32ToF16', 'riscv_f32ToF16', 'riscv_f64ToF16', 'riscv_f16ToF32', 'riscv_f16ToF64', 'riscv_f16ToI64', 'riscv_f16ToUi64', 'riscv_i64ToF16', 'riscv_ui64ToF16', "to_num", "to_vec", "extern_ui64ToF16","extern_i64ToF16","print_insn","num_of_ExceptionType","Ext_DataAddr_OK","pc_alignment_mask","privLevel_to_bits","throw","Error_not_implemented","write_kind_of_flags", "write_ram_ea","mem_write_value_meta","if","vector","ones","to_bits","int_power","valid_segment","valid_vtype","valid_eew_emul","get_scalar","BitStr", "truncate", "slice", "mem_read","write_single_element","signed","Read","Write","match","sail_barrier","get_vtype_vta","__ReadRAM_Meta","Some", "to_str", "MemoryOpResult","MemoryOpResult_add_meta", "MemoryOpResult_drop_meta", "MemException", "MemValue","get_arch_pc", "X", "handle_illegal", "None", "option", "size_bytes", "sizeof", "sign_extend", "zero_extend", "internal_error", "shift_right_arith32", "shift_right_arith64", "assert", "bits", "check_misaligned", "bit_to_bool", "bool_to_bits", "not", "set_next_pc", "get_next_pc","string_take","string_drop","valid_hex_bits","V","zeros","unsigned","ext_check_xret_priv","ext_fail_xret_priv");

all_function_names = Str('riscv_f16MulAdd', 'negate_H', 'canonical_NaN_H', 'riscv_f16Eq', 'riscv_f16Lt', 'riscv_f16Le', 'riscv_f16ToI32', 'riscv_f16ToUi32', 'riscv_i32ToF16', 'riscv_ui32ToF16', 'riscv_f32ToF16', 'riscv_f64ToF16', 'riscv_f16ToF32', 'riscv_f16ToF64', 'riscv_f16ToI64', 'riscv_f16ToUi64', 'riscv_i64ToF16', 'riscv_ui64ToF16', "to_num", "to_vec", "extern_ui64ToF16","extern_i64ToF16","print_insn","num_of_ExceptionType","Ext_DataAddr_OK","pc_alignment_mask","privLevel_to_bits","throw","Error_not_implemented","write_kind_of_flags", "write_ram_ea","mem_write_value_meta","if","vector","ones","to_bits","int_power","valid_segment","valid_vtype","valid_eew_emul","get_scalar","BitStr", "truncate", "slice", "mem_read","write_single_element","signed","Read","Write","sail_barrier","get_vtype_vta","__ReadRAM_Meta","Some", "to_str", "MemoryOpResult","MemoryOpResult_add_meta", "MemoryOpResult_drop_meta", "MemException", "MemValue","get_arch_pc", "X", "handle_illegal", "None", "option", "size_bytes", "sizeof", "sign_extend", "zero_extend", "internal_error", "shift_right_arith32", "shift_right_arith64", "assert", "bits", "check_misaligned", "bit_to_bool", "bool_to_bits", "not", "set_next_pc", "get_next_pc","string_take","string_drop","valid_hex_bits","V","zeros","unsigned","ext_check_xret_priv","ext_fail_xret_priv",'xt2', 'xt3', 'gfmul','isla_footprint_no_init', 'isla_footprint','writeCSR','init_platform', 'ext_init', 'init_sys', 'init_model', 'init_vregs', 'init_base_regs', 'init_masked_result', 'init_masked_source', 'init_masked_result_carry', 'init_masked_result_cmp', 'init_vmem', 'ext_init_regs', 'ext_rvfi_init', 'init_pmp', 'init_TLB', 'init_fdext_regs', 'ext_init','isCSRdefined','main', 'is_CSR_defined', 'aes_mixcolumn_byte_fwd', 'aes_mixcolumn_byte_inv', 'aes_mixcolumn_fwd', 'aes_mixcolumn_inv', 'aes_decode_rcon', 'sbox_lookup', 'aes_sbox_fwd', 'aes_sbox_inv', 'aes_subword_fwd', 'aes_subword_inv', 'sm4_sbox', 'aes_get_column', 'aes_apply_fwd_sbox_to_each_byte', 'aes_apply_inv_sbox_to_each_byte', 'getbyte', 'aes_rv64_shiftrows_fwd', 'aes_rv64_shiftrows_inv', 'aes_shift_rows_fwd', 'aes_shift_rows_inv', 'aes_subbytes_fwd', 'aes_subbytes_inv', 'aes_mixcolumns_fwd', 'aes_mixcolumns_inv', 'csr_name', 'extend_value', 'process_load', 'effective_fence_set', 'timeout_wfi', 'compressed_measure', 'process_vlseg', 'process_vlsegff', 'process_vsseg', 'process_vlsseg', 'process_vssseg', 'process_vlxseg', 'process_vsxseg', 'process_vlre', 'process_vsre', 'process_vm', 'plat_htif_tohost', 'phys_mem_segments', 'within_phys_mem', 'within_clint', 'within_htif', 'clint_load', 'clint_dispatch', 'clint_store', 'tick_clock', 'reset_htif', 'htif_load', 'htif_store', 'htif_tick', 'within_mmio_readable', 'within_mmio_readable', 'within_mmio_writable', 'within_mmio_writable', 'mmio_read', 'mmio_write', 'tick_platform', 'handle_instr_fault', 'handle_virtual_instr', 'platform_wfi', 'get_hstatus_VSXL', 'set_hstatus_VSXL', 'legalize_hstatus', 'legalize_hedeleg', 'legalize_hideleg', 'legalize_hvip', 'lower_mip_to_hvip', 'legalize_hip', 'lower_mip_to_hip', 'legalize_hie', 'lower_mie_to_hie', 'legalize_hcounteren', 'legalize_hgeie', 'legalize_hgatp64', 'legalize_hgatp32', 'get_vsstatus_UXL', 'set_vsstatus_UXL', 'legalize_vsstatus', 'legalize_vsip', 'lower_mip_to_vsip', 'legalize_vsie', 'lower_mie_to_vsie', 'riscv_f16Add', 'riscv_f16Sub', 'riscv_f16Mul', 'riscv_f16Div', 'riscv_f32Add', 'riscv_f32Sub', 'riscv_f32Mul', 'riscv_f32Div', 'riscv_f64Add', 'riscv_f64Sub', 'riscv_f64Mul', 'riscv_f64Div', 'riscv_f32MulAdd', 'riscv_f64MulAdd', 'riscv_f16Sqrt', 'riscv_f32Sqrt', 'riscv_f64Sqrt', 'riscv_f32ToI32', 'riscv_f32ToUi32', 'riscv_i32ToF32', 'riscv_ui32ToF32', 'riscv_f32ToI64', 'riscv_f32ToUi64', 'riscv_i64ToF32', 'riscv_ui64ToF32', 'riscv_f64ToI32', 'riscv_f64ToUi32', 'riscv_i32ToF64', 'riscv_ui32ToF64', 'riscv_f64ToI64', 'riscv_f64ToUi64', 'riscv_i64ToF64', 'riscv_ui64ToF64', 'riscv_f32ToF64', 'riscv_f64ToF32', 'riscv_f16Lt_quiet', 'riscv_f16Le_quiet', 'riscv_f32Lt', 'riscv_f32Lt_quiet', 'riscv_f32Le', 'riscv_f32Le_quiet', 'riscv_f32Eq', 'riscv_f64Lt', 'riscv_f64Lt_quiet', 'riscv_f64Le', 'riscv_f64Le_quiet', 'riscv_f64Eq', 'riscv_f16roundToInt', 'riscv_f32roundToInt', 'riscv_f64roundToInt', 'tick_pc', 'init_hext', 'csr_access_raises_virtual_instr', 'ext_veto_disable_C', 'write_ram', 'read_ram', 'fsplit_H', 'fmake_H', 'fle_H', 'haveHalfFPU', 'ext_fetch_check_pc', 'ext_handle_fetch_check_error', 'ext_control_check_addr', 'ext_control_check_pc', 'ext_handle_control_check_error', 'ext_data_get_addr', 'ext_handle_data_check_error', 'ext_check_phys_mem_read', 'ext_check_phys_mem_write', 'ext_fetch_hook', 'ext_pre_step_hook', 'ext_post_step_hook', 'exception_delegatee', 'findPendingInterrupt', 'translateVSInterrupts', 'processPending', 'getPendingSet', 'dispatchInterrupt', 'exc_causes_transformed_inst_in_xtinst', 'rvfi_trap', 'rvfi_trap', 'trap_handler', 'exception_handler', 'handle_exception', 'handle_mem_exception', 'handle_interrupt', 'is_fiom_active', 'step', 'loop', 'lower_sstatus', 'lift_ustatus', 'legalize_ustatus', 'lower_sip', 'lower_sie', 'lift_uip', 'legalize_uip', 'lift_uie', 'legalize_uie', 'not_bit', 'string_of_bit', 'get_config_print_instr', 'get_config_print_reg', 'get_config_print_mem', 'get_config_print_platform', 'zeros_implicit', 'operator', 'operator', 'operator', 'operator', 'operator', 'rotate_bits_right', 'rotate_bits_left', 'rotater', 'rotatel', 'reverse_bits_in_byte', 'some_or', 'some_or_zero', 'log2', 'isRVC', 'fetch', 'GPRstr', 'initial_analysis', 'initial_analysis', 'empty_exception_context', 'mem_exception_context', 'vmem_exception_context', 'instr_exception_context', 'ext_exception_context', 'virtMode_of_bits', 'virtMode_to_bits', 'virtMode_to_str', 'virt_priv_to_str', 'dirty_v_context', 'dirty_v_context_if_present', 'wV', 'rV_bits', 'wV_bits', 'ext_write_vcsr', 'get_num_elem', 'read_single_vreg', 'write_single_vreg', 'read_vreg', 'read_single_element', 'write_vreg', 'read_vmask', 'read_vmask_carry', 'write_vmask', 'valid_rounding_mode', 'nxFlag', 'ufFlag', 'ofFlag', 'dzFlag', 'nvFlag', 'fsplit_S', 'fmake_S', 'negate_S', 'feq_quiet_S', 'flt_S', 'fle_S', 'haveSingleFPU', 'process_fload64', 'process_fload32', 'process_fload16', 'process_fstore', 'process_rfvv_single', 'process_rfvv_widen', 'ext_decode_compressed', 'ext_decode', 'hex_bits_forwards', 'hex_bits_forwards_matches', 'hex_bits_backwards', 'hex_bits_backwards_matches', 'rvfi_wX', 'rvfi_wX', 'wX', 'rX_bits', 'wX_bits', 'reg_name_abi', 'assert_vstart', 'valid_fp_op', 'valid_rd_mask', 'valid_reg_overlap', 'illegal_normal', 'illegal_vd_masked', 'illegal_vd_unmasked', 'illegal_variable_width', 'illegal_reduction', 'illegal_reduction_widen', 'illegal_fp_normal', 'illegal_fp_vd_masked', 'illegal_fp_vd_unmasked', 'illegal_fp_variable_width', 'illegal_fp_reduction', 'illegal_fp_reduction_widen', 'illegal_load', 'illegal_store', 'illegal_indexed_load', 'illegal_indexed_store', 'get_start_element', 'get_end_element', 'can', 'read_vreg_seg', 'canonical_NaN', 'f_is_neg_inf', 'f_is_neg_norm', 'f_is_neg_subnorm', 'f_is_neg_zero', 'f_is_pos_zero', 'f_is_pos_subnorm', 'f_is_pos_norm', 'f_is_pos_inf', 'f_is_SNaN', 'f_is_QNaN', 'f_is_NaN', 'get_scalar_fp', 'get_shift_amount', 'get_fixed_rounding_incr', 'unsigned_saturation', 'signed_saturation', 'get_fp_rounding_mode', 'negate_fp', 'fp_add', 'fp_sub', 'fp_min', 'fp_max', 'fp_eq', 'fp_gt', 'fp_ge', 'fp_lt', 'fp_le', 'fp_mul', 'fp_div', 'fp_muladd', 'fp_nmuladd', 'fp_mulsub', 'fp_nmulsub', 'fp_class', 'fp_widen', 'riscv_f16ToI16', 'riscv_f16ToI8', 'riscv_f32ToI16', 'riscv_f16ToUi16', 'riscv_f16ToUi8', 'riscv_f32ToUi16', 'count_leadingzeros', 'rsqrt7', 'riscv_f16Rsqrte7', 'riscv_f32Rsqrte7', 'riscv_f64Rsqrte7', 'recip7', 'riscv_f16Recip7', 'riscv_f32Recip7', 'riscv_f64Recip7', 'fsplit_D', 'fmake_D', 'negate_D', 'feq_quiet_D', 'flt_D', 'fle_D', 'haveDoubleFPU', 'validDoubleRegs', 'aqrl_str', 'lrsc_width_str', 'amo_width_valid', 'process_loadres', 'legalize_misa', 'haveAtomics', 'haveRVC', 'haveMulDiv', 'haveSupMode', 'haveUsrMode', 'haveNExt', 'haveHExt', 'haveZba', 'haveZbb', 'haveZbc', 'haveZbs', 'haveZfa', 'haveZbkb', 'haveZbkc', 'haveZbkx', 'haveZkr', 'haveZksh', 'haveZksed', 'haveZknh', 'haveZkne', 'haveZknd', 'haveZmmul', 'haveZicond', 'get_mstatus_SXL', 'set_mstatus_SXL', 'get_mstatus_UXL', 'set_mstatus_UXL', 'get_mstatus_GVA', 'set_mstatus_GVA', 'set_mstatush_GVA', 'get_mstatus_MPV', 'set_mstatus_MPV', 'set_mstatush_MPV', 'effectivePrivilege', 'effectiveVirtualization', 'legalize_mstatus', 'cur_Architecture', 'in32BitMode', 'haveFExt', 'haveDExt', 'haveZfh', 'haveVExt', 'haveZhinx', 'haveZfinx', 'haveZdinx', 'legalize_mip', 'legalize_mie', 'legalize_mideleg', 'legalize_medeleg', 'legalize_tvec', 'tvec_addr', 'legalize_xepc', 'legalize_counteren', 'legalize_mcounteren', 'legalize_scounteren', 'legalize_mcountinhibit', 'retire_instruction', 'get_sstatus_UXL', 'set_sstatus_UXL', 'lower_mstatus', 'lift_sstatus', 'legalize_sstatus', 'legalize_sedeleg', 'lower_mip_to_sip', 'lower_mie', 'lift_sip', 'legalize_sip', 'lift_sie', 'legalize_sie', 'legalize_satp64', 'legalize_satp32', 'read_seed_csr', 'write_seed_csr', 'legalize_envcfg', 'get_sew_pow', 'get_sew', 'get_sew_bytes', 'get_lmul_pow', 'decode_agtype', 'get_vtype_vma', '__WriteRAM_Meta', 'regidx_to_regno', 'creg2reg_idx', 'architecture', 'arch_to_bits', 'not_implemented', 'privLevel_of_bits', 'privLevel_to_str', 'AccessType_to_str', 'interruptType_to_bits', 'interruptType_to_str', 'exceptionType_to_bits', 'exceptionType_to_str', 'E_Addr_Align_of_AccessType', 'E_Access_Fault_of_AccessType', 'E_Page_Fault_of_AccessType', 'E_GPage_Fault_of_AccessType', 'exceptionType_update_AccessType', 'trapCause_to_bits', 'trapCause_is_interrupt', 'trapCause_to_str', 'trapVectorMode_of_bits', 'extStatus_to_bits', 'extStatus_of_bits', 'AddressTranslationStage_to_str', 'satp64Mode_of_bits', 'hgatp64Mode_of_bits', 'AddressTranslationMode_to_str', 'report_invalid_width', 'can', 'undefined_SV_Params', 'vpns_of_va', 'vpn_j_of_va', 'offset_of_va', 'is_valid_vAddr', 'msbs_of_PTE', 'PPNs_of_PTE', 'pte_is_ptr', 'pte_is_invalid', 'check_PTE_permission', 'update_PTE_Bits', 'legalize_satp', 'satp_to_asid', 'satp_to_PT_base', 'legalize_hgatp', 'hgatp_to_vmid', 'hgatp_to_PT_base', 'translationMode', 'implicit_error', 'ptw_error_to_str', 'ext_get_ptw_error', 'translationException', 'pseudoinst', 'translationEContext', 'pt_walk', 'translate_TLB_hit', 'translate_TLB_miss', 'translate', 'translate_stage', 'GStage_exception', 'translateAddr_pv', 'translateAddr', 'FRegStr', 'fregval_from_freg', 'fregval_into_freg', 'csrAccess', 'csrPriv', 'is_CSR_defined', 'check_CSR_access', 'check_TVM_SATP', 'check_Counteren', 'check_seed_CSR', 'check_CSR', 'ext_check_CSR', 'ext_check_CSR_fail', 'is_aligned_addr', 'read_kind_of_flags', 'phys_mem_read', 'checked_mem_read', 'pmp_mem_read', 'rvfi_read', 'rvfi_read', 'mem_read_priv_meta', 'mem_read_meta', 'mem_read_priv', 'mem_write_ea', 'rvfi_write', 'rvfi_write', 'phys_mem_write', 'checked_mem_write', 'pmp_mem_write', 'mem_write_value_priv_meta', 'mem_write_value_priv', 'mem_write_value', 'pmpAddrRange', 'pmpCheckRWX', 'pmpCheckPerms', 'pmpMatchAddr', 'pmpMatchEntry', 'pmpCheck', 'get_elen_pow', 'get_vlen_pow', 'spc_forwards', 'spc_forwards_matches', 'spc_backwards', 'opt_spc_forwards', 'opt_spc_forwards_matches', 'opt_spc_backwards', 'opt_spc_backwards_matches', 'def_spc_forwards', 'def_spc_forwards_matches', 'def_spc_backwards', 'def_spc_backwards_matches', 'pmpAddrMatchType_of_bits', 'pmpAddrMatchType_to_bits', 'pmpReadCfgReg', 'pmpLocked', 'pmpTORLocked', 'pmpWriteCfg', 'pmpWriteCfgReg', 'pmpWriteAddr', 'fetch', 'handle_trap_extension', 'get_xret_target', 'set_xret_target', 'prepare_xret_target', 'get_mtvec', 'get_stvec', 'get_vstvec', 'get_utvec', 'set_mtvec', 'set_stvec', 'set_vstvec', 'set_utvec', 'get_trap_vector', 'set_trap_vector', 'prepare_trap_vector', 'fcvtmod_helper', 'write_TLB', 'match_TLB_Entry', 'flush_TLB_Entry', 'lookup_TLB', 'add_to_TLB', 'flush_TLB', 'RegStr', 'regval_from_reg', 'regval_into_reg', 'canonical_NaN_S', 'canonical_NaN_D', 'dirty_fd_context', 'dirty_fd_context_if_present', 'wF', 'rF_bits', 'wF_bits', 'rF_H', 'wF_H', 'rF_S', 'wF_S', 'rF_D', 'wF_D', 'rF_or_X_H', 'rF_or_X_S', 'rF_or_X_D', 'wF_or_X_H', 'wF_or_X_S', 'wF_or_X_D', 'ext_write_fcsr', 'accrue_fflags', 'rvfi_set_instr_packet', 'rvfi_get_cmd', 'rvfi_get_insn', 'print_instr_packet', 'rvfi_zero_exec_packet', 'rvfi_halt_exec_packet', 'rvfi_get_v2_support_packet', 'rvfi_get_exec_packet_v1', 'rvfi_get_v2_trace_size', 'rvfi_get_exec_packet_v2', 'rvfi_get_int_data', 'rvfi_get_mem_data', 'rvfi_encode_width_mask', 'print_rvfi_exec', 'ext_fetch_hook', 'ext_pre_step_hook', 'ext_post_step_hook', 'ext_translate_exception', 'ext_exc_type_to_bits', 'num_of_ext_exc_type', 'ext_exc_type_to_str');

# --------------------------------- Patterns for identifying instruction definitions and function calls -------------------------------------------------- #

# neeluk: These are pattern constructors that we can use while specifying a Lexicon. 

instruction_definition_start = Str("function clause execute") + Str("", " ", "(", " (", "( ", " ( ");
instruction_definition = instruction_definition_start + Str(*instruction_names);

function_call_start = Str("(", " (");
# Args should be analysed even for functions_to_ignore? 

# TODO: Functions_to_ignore and all_function_names

function_call = all_function_names + function_call_start; 
function_definition_start = Str("function ") + Str("", " ");
function_definition = function_definition_start + Str(*function_names); 

#augmented_function_defintion = function_definition_start + Str(*augmented_function_names);

# ------------------------------------ Patterns for matching expressions to identify Read vs. Write use of the CSR --------------------------------------- #

csr_read_match_clause = Str("match") + Rep(AnyBut('{')) + Str(*ctrl_reg_names) + Rep(AnyBut('{')) + Str("{");
csr_read_for_comparison_rhs = comparison_operators + Str("", " ", "(") + Str(*ctrl_reg_names);
csr_read_for_comparison_lhs = Str(*ctrl_reg_names) + Str("", " ", ")") + comparison_operators; 
csr_read_if_clause_1 = Str("if") + Rep(AnyBut('{\n;')) + Str(*ctrl_reg_names) + Rep(AnyBut('{\n;')) + Str("then", ";");  # TODO: Added '\n' here because otherwise it doesn't even ignore "then" and continues scanning the pattern until a new opening braces is found..... not ideal. 
csr_read_if_clause_2 = Str("if") + Rep(AnyBut('{\n;')) + Str(*ctrl_reg_names) + Rep(AnyBut('{\n;')) + Str("{", ";"); #TODO: Added '\n' here too. This is a bit annoying. The problem is if .... then .... which doesn't contain any opening braces. How about ";"? 
csr_read_instance_1 = Str("=") + AnyBut('>') + Rep(AnyBut("=;\n")) + Str(*ctrl_reg_names); 

# csr_read_instance_1 = Str("=") + Rep(Str(""," ","(")) + csr_list + Rep(Str(""," ",")")); # Used as the first operand in RHS of expression 
# csr_read_instance_2 = Str("=") + Rep(Str(""," ", "(")) +  Rep(Str(""," ",")")) + operators + Rep(Str(""," ","(")) + csr_list + Rep(Str(""," ",")"));
# csr_read_instance_2 = Str("=") + Rep(Str(""," ")) + Rep((name | csr_list) + operators) + Rep(Str(""," ","("))csr_list; # Used somewhere in the RHS of expression 
# csr_read_instance_3 : argument to function call, specified as a new state in the lexicon to scan function call arguments.

# Str("=") + Rep(AnyBut(csr_list, Str("\n"), Str("="))) + csr_list

# + Rep(name | open_parenthesis | close_parenthesis

csr_write_instance_1 = Rep(Str(""," ")) + Str("","(") + Str(*ctrl_reg_names) + Rep(Str(""," ")) + Str("",")") + Str("="); # LHS of expression 

csr_read_and_write_instance = Str("", " ", "(") + Str(*ctrl_reg_names) + Rep(Str(""," ")) + Str("",")") + Str("=") + Rep(AnyBut("=;\n")) + Str(*ctrl_reg_names); 


# --------------------------------------- RISC-V specific list of CSRs, instructions, and Sail functions ------------------------------------------------ #

def find_instruction_names():
    global instruction_definition;
    with os.popen('grep -nr "function clause execute" '+sail_model_dir) as res:
        for instr_def in res:
            # Ensure there is a "= {" i.e. execute definition start, else ignore.
            # Note: Several instructions end with "= RETIRE_SUCCESS" definitions. We ignore those.
            # Note: Instructions implemented in the "cext" eventually call execute of other instructions which we are analysing.
            # Note: These (cext) instructions do not use any privilege information explicitly, so analysing just the instruction's implementation they execute is enough (e.g. ebreak for c_ebreak). So, we ignore these.
            # Note: The only exception which is excluded by the following condition is "WFI". We analyse that one manually.
            if "= {" not in instr_def:
                continue;

            if "handle_illegal" in instr_def or "execute CSR(" in instr_def:
                continue;

            instr_def_split = instr_def.split(":");
            instr_file_name = instr_def_split[0];
            #instr_line_num = int(instr_def_split[1]);
            instr_name = "";
            if "execute(" in instr_def_split[2]:
                instr_name = instr_def_split[2].split("execute(")[1].split("=")[0];
            elif "execute (" in instr_def_split[2]:
                instr_name = instr_def_split[2].split("execute (")[1].split("=")[0];
            else:
                instr_name = instr_def_split[2].split("execute")[1].split("=")[0];

            instr_name = instr_name.split("(")[0].replace(" ", "");

            #print(instr_def);
            instruction_names.append(instr_name);
            if instr_file_name not in files_to_scan_for_instr_defs:
                files_to_scan_for_instr_defs.append(instr_file_name);

    instruction_definition = instruction_definition_start + Str(*instruction_names);

def find_function_names():
    global function_definition;
    with os.popen('grep -nr "function " '+sail_model_dir+' | grep -v "execute" | grep -v "clause" | grep -v "scattered"') as res:
        for fn_def in res:
            if "(" not in fn_def:
                continue;
            #print(fn_def);
            fn_def_split = fn_def.split(":");
            fn_file_name = fn_def_split[0];
            fn_line_num = int(fn_def_split[1]);
            fn_name = fn_def_split[2].split("(")[0];
            if fn_name.find("function", 0) == -1:
                continue;
            fn_name = fn_name.split("function ")[1].split(" ")[0];
            if fn_name not in functions_to_ignore:
                function_names.append(fn_name);
                if fn_file_name not in files_to_scan_for_func_defs:
                    files_to_scan_for_func_defs.append(fn_file_name);

    function_definition = function_definition_start + Str(*function_names); 


def find_ctrl_reg_names():
    with os.popen('grep -nr "mapping clause csr_name_map" '+sail_model_dir) as res:
        for csr_name_map in res: 
            if '"' in csr_name_map: 
                csr_name = csr_name_map.split('"')[1]; 
                initial_ctrl_reg_names.append(csr_name);

def find_ctrl_reg_bitfields(csr_name):
    global csr_read_and_write_instance;
    global csr_read_if_clause_1;
    global csr_read_if_clause_2;
    global csr_read_for_comparison_lhs;
    global csr_read_for_comparison_rhs;
    global csr_read_match_clause;
    global csr_read_instance_1;
    global csr_write_instance_1;
    global ctrl_reg_names;

    bitfield_def = os.popen('grep -nri "bitfield '+csr_name+' " '+sail_model_dir).read();

    # if response is null, then there is no bitfield. Return.
    if bitfield_def == "":
        return;

    if len(bitfield_def.split("\n")) > 2:
        print("Found too many bitfield definitions for "+csr_name);
        print(bitfield_def)
        print(bitfield_def.split("\n"))
        exit(0);

    bitfield_def_split = bitfield_def.split(":");

    file_path = bitfield_def_split[0];
    line = bitfield_def_split[1];

    in_file = open(file_path, 'r');
    in_file_lines = in_file.readlines();
    in_file.close();

    line_no = int(line)
    cur_line = in_file_lines[line_no];
    
    while "}" not in cur_line:
        if "//" not in cur_line and cur_line != "\n":
            cur_line_words = cur_line.split(":");
            field = cur_line_words[0].replace(" ","");
            ctrl_reg_names.append(csr_name+"["+field+"]");

        line_no = line_no + 1;
        cur_line = in_file_lines[line_no];

    csr_read_match_clause = Str("match") + Rep(AnyBut('{')) + Str(*ctrl_reg_names) + Rep(AnyBut('{')) + Str("{");
    csr_read_for_comparison_rhs = comparison_operators + Str("", " ", "(") + Str(*ctrl_reg_names);
    csr_read_for_comparison_lhs = Str(*ctrl_reg_names) + Str("", " ", ")") + comparison_operators; 
    csr_read_if_clause_1 = Str("if") + Rep(AnyBut('{\n;')) + Str(*ctrl_reg_names) + Rep(AnyBut('{\n;')) + Str("then", ";");  # TODO: Added '\n' here because otherwise it doesn't even ignore "then" and continues scanning the pattern until a new opening braces is found..... not ideal. 
    csr_read_if_clause_2 = Str("if") + Rep(AnyBut('{\n;')) + Str(*ctrl_reg_names) + Rep(AnyBut('{\n;')) + Str("{", ";"); #TODO: Added '\n' here too. This is a bit annoying. The problem is if .... then .... which doesn't contain any opening braces. How about ";"? 
    csr_read_instance_1 = Str("=") + AnyBut('>') + Rep(AnyBut("=;\n")) + Str(*ctrl_reg_names); 

    # csr_read_instance_1 = Str("=") + Rep(Str(""," ","(")) + csr_list + Rep(Str(""," ",")")); # Used as the first operand in RHS of expression 
    # csr_read_instance_2 = Str("=") + Rep(Str(""," ", "(")) +  Rep(Str(""," ",")")) + operators + Rep(Str(""," ","(")) + csr_list + Rep(Str(""," ",")"));
    # csr_read_instance_2 = Str("=") + Rep(Str(""," ")) + Rep((name | csr_list) + operators) + Rep(Str(""," ","("))csr_list; # Used somewhere in the RHS of expression 
    # csr_read_instance_3 : argument to function call, specified as a new state in the lexicon to scan function call arguments.

    # Str("=") + Rep(AnyBut(csr_list, Str("\n"), Str("="))) + csr_list

    # + Rep(name | open_parenthesis | close_parenthesis

    csr_write_instance_1 = Rep(Str(""," ")) + Str("","(") + Str(*ctrl_reg_names) + Rep(Str(""," ")) + Str("",")") + Str("="); # LHS of expression 

    csr_read_and_write_instance = Str("", " ", "(") + Str(*ctrl_reg_names) + Rep(Str(""," ")) + Str("",")") + Str("=") + Rep(AnyBut("=;\n")) + Str(*ctrl_reg_names); 

    return;

def process_csr_access_to_csv():
    CSR_access_results_file = open(results_dir+"/scanner-results/riscv64-hext/csr_access.txt", "r");
    CSR_access_results_file_lines = CSR_access_results_file.readlines();
    line_index = 0;

    csv_output_file = open(results_dir+'/scanner-results/riscv64-hext/priv-levels-csr-access.csv', 'w', newline='');
    first_row = ["CSR", "U-mode Read", "U-mode Write", "VU-mode Read", "VU-mode Write", "HS-mode Read", "HS-mode Write", "VS-mode Read", "VS-mode Write", "M-mode Read", "M-mode Write"];
    csv_writer = csv.writer(csv_output_file);
    csv_writer.writerow(first_row);

    while "Printing CSR Access Results" not in CSR_access_results_file_lines[line_index]: 
        line_index = line_index + 1;

    # Start parsing 
    line_index = line_index + 1;

    # These are typically not allowed any access as they are for 32 bit platforms. So we should just ignore. 
    csrs_to_ignore = ["mcycleh", "minstreth", "timeh", "instreth", "cycleh"];

    while "DONE Printing CSR Access Results" not in CSR_access_results_file_lines[line_index]: 
        cur_line = CSR_access_results_file_lines[line_index];
        cur_line = cur_line.replace("\n","").replace(":","");
        if cur_line in initial_ctrl_reg_names or cur_line == "frm": 
            # New CSR record. 
            m_rd = "False"; m_wr = "False"; hs_rd = "False"; hs_wr = "False"; vs_rd = "False"; vs_wr = "False"; u_rd = "False"; u_wr = "False"; vu_rd = "False"; vu_wr = "False";
            # Skip line with string "M-mode"
            line_index = line_index + 2;
            # M-mode Read 
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Readable": 
                m_rd = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Readable":
                m_rd = "False";
            else: 
                print("No match for M-mode read");
                exit(0);
            # M-mode Write
            line_index = line_index + 1;
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Writable": 
                m_wr = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Writable":
                m_wr = "False";
            else: 
                print("No match for M-mode write");
                exit(0);
            
            # Skip line with string "HS-mode"
            line_index = line_index + 2;
            # HS-mode Read 
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Readable": 
                hs_rd = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Readable":
                hs_rd = "False";
            else: 
                print("No match for S-mode read");
                exit(0);
            # HS-mode Write
            line_index = line_index + 1;
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Writable": 
                hs_wr = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Writable":
                hs_wr = "False";
            else: 
                print("No match for S-mode write");
                exit(0);

            # Skip line with string "VS-mode"
            line_index = line_index + 2;
            # VS-mode Read 
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Readable": 
                vs_rd = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Readable":
                vs_rd = "False";
            else: 
                print("No match for VS-mode read");
                exit(0);
            # VS-mode Write
            line_index = line_index + 1;
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Writable": 
                vs_wr = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Writable":
                vs_wr = "False";
            else: 
                print("No match for VS-mode write");
                exit(0);

            # Skip line with string "U-mode"
            line_index = line_index + 2;
            # U-mode Read 
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Readable": 
                u_rd = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Readable":
                u_rd = "False";
            else: 
                print("No match for U-mode read");
                exit(0);
            # U-mode Write
            line_index = line_index + 1;
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Writable": 
                u_wr = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Writable":
                u_wr = "False";
            else: 
                print("No match for U-mode write");
                exit(0);

            # Skip line with string "VU-mode"
            line_index = line_index + 2;
            # VU-mode Read 
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Readable": 
                vu_rd = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Readable":
                vu_rd = "False";
            else: 
                print("No match for U-mode read");
                exit(0);
            # VU-mode Write
            line_index = line_index + 1;
            if CSR_access_results_file_lines[line_index].replace("\n","") == "Writable": 
                vu_wr = "True";
            elif CSR_access_results_file_lines[line_index].replace("\n","") == "Not Writable":
                vu_wr = "False";
            else: 
                print("No match for U-mode write");
                exit(0);

            # TODO: Is this needed?
            if cur_line == "frm":
                cur_line = "fcsr[FRM]";
            
            if u_rd == "False" and u_wr == "False" and hs_rd == "False" and hs_wr == "False" and m_rd == "False" and m_wr == "False" and vu_rd == "False" and vu_wr == "False" and vs_rd == "False" and vs_wr == "False": 
                print("All permissions false for CSR: "+cur_line);
                if cur_line not in csrs_to_ignore: 
                    # Setting true, as either extension flags not being set are making these false (like Next) or extensions do not define privilege access criteria (like for fcsr).
                    if cur_line == "vsedeleg" or "vsideleg": 
                        hs_rd = "True"; hs_wr = "True"; m_rd = "True"; m_wr = "True";
                    elif cur_line == "sedeleg" or "sideleg": 
                        hs_rd = "True"; hs_wr = "True"; m_rd = "True"; m_wr = "True"; vs_rd = "True"; vs_wr = "True";
                    else:
                        u_rd = "True"; u_wr = "True"; hs_rd = "True"; hs_wr = "True"; m_rd = "True"; m_wr = "True"; vs_rd = "True"; vs_wr = "True"; vu_rd = "True"; vu_wr = "True";
            
            # Finally create the row and write to the CSV 
            csr_record = [cur_line, u_rd, u_wr, vu_rd, vu_wr, hs_rd, hs_wr, vs_rd, vs_wr, m_rd, m_wr];
            csv_writer.writerow(csr_record);
            
        else: 
            if cur_line == "0x101" or cur_line == "0xf15" or cur_line == "0x30a" or cur_line == "0x10a":
                line_index = line_index + 16; # Skip this record.
                # Todo: translate these into csr name mappings manually instead of skipping.
                continue;
            
            print("Unexpected line found which is not a CSR: "+cur_line);
            exit(0);
        line_index = line_index + 1;

def arch_init(argv_sail_dir, argv_sail_model_dir, argv_results_dir):
    global sail_model_dir;
    global results_dir;
    print("Initializing RISC-V H-ext Arch!");
    
    sail_model_dir = argv_sail_model_dir;
    results_dir = argv_results_dir;

    find_instruction_names();
    print("Instruction names: ");
    print(instruction_names);
    
    find_function_names();
    print("Function names: ");
    print(function_names);

    find_ctrl_reg_names();
    print("CSR names: ");
    print(initial_ctrl_reg_names);
    
    for ctrl_reg in initial_ctrl_reg_names:
        find_ctrl_reg_bitfields(ctrl_reg)
        ctrl_reg_names.append(ctrl_reg);

    print("CSR names with bitfields: ");
    print(ctrl_reg_names);


def arch_ctrl_reg_access():
    # Run the command to execute add instr in sail-riscv 
    # It will generate a csr_access.txt file which will be processed later to be converted to a CSV
    
    #os.popen('cd ../../riscv-hext-sail/ && make csim && cd ../sailor/src/');
    #os.popen('cd ../../riscv-hext-sail/ && ./c_emulator/riscv_sim_RV64  test/riscv-tests/rv64ui-p-add.elf > ../sailor/results/scanner-results/riscv_hext_csr_access.txt && cd ../sailor/src/');

    process_csr_access_to_csv();


def dictionaries_to_csv(user, user_v, supervisor, supervisor_v, machine, output_file):
  """Converts three dictionaries with identical keys into a CSV file.
  """
  with open(output_file, 'w', newline='') as csvfile:
    fieldnames = ['Instruction','U-mode Executable','VU-mode Executable', 'HS-mode Executable', 'VS-mode Executable', 'Machine Executable'];
    writer = csv.DictWriter(csvfile, fieldnames=fieldnames);
    writer.writeheader();
    for key in user.keys():
      writer.writerow({'Instruction': key, 'U-mode Executable': user[key], 'VU-mode Executable': user_v[key], 'HS-mode Executable': supervisor[key], 'VS-mode Executable': supervisor_v[key], 'Machine Executable': machine[key]});

def arch_instr_access():
    for file_name in files_to_scan_for_instr_defs:
        print("Scanning "+file_name);
        f = open(file_name, 'r');
        scanner = RISCV_Sail_Scanner(f, file_name);
        while 1:
            token = scanner.read();
            file_name, line_number, char_number = scanner.position();
            print(file_name);
            print(line_number);
            print(char_number);
            print(token);
            if token[0] is None:
                print("Token is none");
                break;
        f.close();
    
    dictionaries_to_csv(instruction_executable[0], instruction_executable[1], instruction_executable[2], instruction_executable[3],  instruction_executable[4],results_dir+"/scanner-results/riscv64-hext/priv-levels-instruction-execution.csv");


