# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #

from plex import *;
from sail_syntax import *;
#from riscv import *;
from importlib import import_module;

# ------------------------------------------------ Basic regex for words/names, comments, spaces --------------------------------------------------------- #

letter = Range("AZaz");
digit = Range("09");
underscore = Str("_");
open_square_bracket = Str("[");
close_square_bracket = Str("]");
name = letter + Rep(letter | digit | underscore | open_square_bracket | close_square_bracket);

#open_parenthesis = Str("(");
#close_parenthesis = Str(")");

# neeluk: We don't expect nested comments. If they exist in the Sail code, the analysis results might gather some noise. 
small_comment = Str("//") + Rep(AnyBut("\n")) + Str("\n");

# --------------------------------------------------------- Output of the analysis ---------------------------------------------------------------------- #

# I guess 5 will work for most use-cases: (M/S/U), (M/HS/VS/VU/U), (EL0-3). 
instruction_executable = [{}, {}, {}, {}, {}];

# ----------------------------------------------------- Intermediate state tracking ---------------------------------------------------------------------- #

current_instruction_being_scanned = "";
current_function_being_scanned = "";
scanning_instruction_definition = False; 
scanning_function_definition = False; 
previous_scanner_state = '';    # This is the default state anyway..... 
parenthesis_to_match = [];
braces_to_match = [];

# ----------------------------------------------------- RISC-V Specific Initialization ------------------------------------------------------------------- #


arch_priv_mode_names = ["User", "Supervisor", "Reserved", "Machine"];
priv_level_symbol = ["cur_privilege"];
instr_exec_fail = ["RETIRE_FAIL"];
instr_exec_success = ["RETIRE_SUCCESS"];

all_instruction_names = Str('UTYPE', 'RISCV_JAL', 'BTYPE', 'ITYPE', 'SHIFTIOP', 'RTYPE', 'LOAD', 'STORE', 'ADDIW', 'RTYPEW', 'SHIFTIWOP', 'FENCE', 'FENCE_TSO', 'FENCEI', 'ECALL', 'MRET', 'SRET', 'EBREAK', 'SFENCE_VMA', 'VLSEGTYPE', 'VLSEGFFTYPE', 'VSSEGTYPE', 'VLSSEGTYPE', 'VSSSEGTYPE', 'VLUXSEGTYPE', 'VLOXSEGTYPE', 'VSUXSEGTYPE', 'VSOXSEGTYPE', 'VLRETYPE', 'VSRETYPE', 'VMTYPE', 'ZBS_IOP', 'ZBS_RTYPE', 'RISCV_JALR', 'RISCV_XPERM8', 'RISCV_XPERM4', 'F_BIN_RM_TYPE_H', 'F_MADD_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_TYPE_H', 'F_UN_TYPE_H', 'F_UN_TYPE_H', 'SHA256SIG0', 'SHA256SIG1', 'SHA256SUM0', 'SHA256SUM1', 'AES32ESMI', 'AES32ESI', 'AES32DSMI', 'AES32DSI', 'SHA512SIG0H', 'SHA512SIG0L', 'SHA512SIG1H', 'SHA512SIG1L', 'SHA512SUM0R', 'SHA512SUM1R', 'AES64KS1I', 'AES64KS2', 'AES64IM', 'AES64ESM', 'AES64ES', 'AES64DSM', 'AES64DS', 'SHA512SIG0', 'SHA512SIG1', 'SHA512SUM0', 'SHA512SUM1', 'RISCV_JALR', 'SINVAL_VMA', 'SFENCE_W_INVAL', 'SFENCE_INVAL_IR', 'C_ADDI4SPN', 'C_LW', 'C_LD', 'C_SW', 'C_SD', 'C_ADDI', 'C_LI', 'C_ADDI16SP', 'C_LUI', 'C_SRLI', 'C_SRAI', 'C_ANDI', 'C_SUB', 'C_XOR', 'C_OR', 'C_AND', 'C_SUBW', 'C_ADDW', 'C_LWSP', 'C_LDSP', 'C_SWSP', 'C_SDSP', 'LOAD_FP', 'STORE_FP', 'F_MADD_TYPE_S', 'F_BIN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_UN_TYPE_S', 'F_UN_TYPE_S', 'F_UN_TYPE_S', 'RIVVTYPE', 'RMVVTYPE', 'RFVVTYPE', 'C_FLWSP', 'C_FSWSP', 'C_FLW', 'C_FSW', 'C_LBU', 'C_LHU', 'C_LH', 'C_SB', 'C_SH', 'C_ZEXT_B', 'C_SEXT_B', 'C_ZEXT_H', 'C_SEXT_H', 'C_ZEXT_W', 'C_NOT', 'C_MUL', 'RISCV_SLLIUW', 'ZBA_RTYPEUW', 'ZBA_RTYPE', 'F_MADD_TYPE_D', 'F_BIN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_UN_TYPE_D', 'F_UN_TYPE_D', 'F_UN_TYPE_D', 'LOADRES', 'STORECON', 'AMO', 'RISCV_CLMUL', 'RISCV_CLMULH', 'RISCV_CLMULR', 'ZBKB_RTYPE', 'ZBKB_PACKW', 'RISCV_ZIP', 'RISCV_UNZIP', 'RISCV_BREV8', 'MUL', 'DIV', 'REM', 'MULW', 'DIVW', 'REMW', 'URET', 'RISCV_RORIW', 'RISCV_RORI', 'ZBB_RTYPEW', 'ZBB_RTYPE', 'ZBB_EXTOP', 'RISCV_REV8', 'RISCV_ORCB', 'RISCV_CPOP', 'RISCV_CPOPW', 'RISCV_CLZ', 'RISCV_CLZW', 'RISCV_CTZ', 'RISCV_CTZW', 'ZICOND_RTYPE', 'ZICOND_RTYPE', 'VVMTYPE', 'VVMCTYPE', 'VVMSTYPE', 'VVCMPTYPE', 'VXMTYPE', 'VXMCTYPE', 'VXMSTYPE', 'VXCMPTYPE', 'VIMTYPE', 'VIMCTYPE', 'VIMSTYPE', 'VICMPTYPE', 'FVVMTYPE', 'FVFMTYPE', 'MMTYPE', 'VCPOP_M', 'VFIRST_M', 'VMSBF_M', 'VMSIF_M', 'VMSOF_M', 'VIOTA_M', 'VID_V', 'C_FLDSP', 'C_FSDSP', 'C_FLD', 'C_FSD', 'RISCV_FLI_H', 'RISCV_FLI_S', 'RISCV_FLI_D', 'RISCV_FMINM_H', 'RISCV_FMAXM_H', 'RISCV_FMINM_S', 'RISCV_FMAXM_S', 'RISCV_FMINM_D', 'RISCV_FMAXM_D', 'RISCV_FROUND_H', 'RISCV_FROUNDNX_H', 'RISCV_FROUND_S', 'RISCV_FROUNDNX_S', 'RISCV_FROUND_D', 'RISCV_FROUNDNX_D', 'RISCV_FMVH_X_D', 'RISCV_FMVP_D_X', 'RISCV_FLEQ_H', 'RISCV_FLTQ_H', 'RISCV_FLEQ_S', 'RISCV_FLTQ_S', 'RISCV_FLEQ_D', 'RISCV_FLTQ_D', 'RISCV_FCVTMOD_W_D', 'VSETVLI', 'VSETVL', 'VSETIVLI', 'SM3P0', 'SM3P1', 'SM4ED', 'SM4KS', 'VVTYPE', 'NVSTYPE', 'NVTYPE', 'MASKTYPEV', 'MOVETYPEV', 'VXTYPE', 'NXSTYPE', 'NXTYPE', 'VXSG', 'MASKTYPEX', 'MOVETYPEX', 'VITYPE', 'NISTYPE', 'NITYPE', 'VISG', 'MASKTYPEI', 'MOVETYPEI', 'VMVRTYPE', 'MVVTYPE', 'MVVMATYPE', 'WVVTYPE', 'WVTYPE', 'WMVVTYPE', 'VEXT2TYPE', 'VEXT4TYPE', 'VEXT8TYPE', 'VMVXS', 'MVVCOMPRESS', 'MVXTYPE', 'MVXMATYPE', 'WVXTYPE', 'WXTYPE', 'WMVXTYPE', 'VMVSX', 'FVVTYPE', 'FVVMATYPE', 'FWVVTYPE', 'FWVVMATYPE', 'FWVTYPE', 'VFUNARY0', 'VFWUNARY0', 'VFNUNARY0', 'VFUNARY1', 'VFMVFS', 'FVFTYPE', 'FVFMATYPE', 'FWVFTYPE', 'FWVFMATYPE', 'FWFTYPE', 'VFMERGE', 'VFMV', 'VFMVSF');
instruction_definition_start = Str("function clause execute") + Str("", " ", "(", " (", "( ", " ( ");
instruction_definition = instruction_definition_start + all_instruction_names;


# ----------------------------------------------------- RISC-V H-ext Specific Initialization -------------------------------------------------------------- #


#arch_priv_mode_names = ["User", "Supervisor", "Reserved", "Machine"];
# arch_priv_mode_names = ["(User, V0)", "(User, V1)", "(Supervisor, V0)", "(Supervisor, V1)", "(Machine, _)", "Machine"];
# priv_level_symbol = ["cur_privilege"];
# instr_exec_fail = ["RETIRE_FAIL", "E_Illegal_Instr"];
# instr_exec_success = ["RETIRE_SUCCESS"];

# all_instruction_names = Str('UTYPE', 'RISCV_JAL', 'BTYPE', 'ITYPE', 'SHIFTIOP', 'RTYPE', 'LOAD', 'STORE', 'ADDIW', 'RTYPEW', 'SHIFTIWOP', 'FENCE', 'FENCE', 'FENCE_TSO', 'FENCE_TSO', 'FENCEI', 'ECALL', 'MRET', 'SRET', 'EBREAK', 'SFENCE_VMA', 'VLSEGTYPE', 'VLSEGFFTYPE', 'VSSEGTYPE', 'VLSSEGTYPE', 'VSSSEGTYPE', 'VLUXSEGTYPE', 'VLOXSEGTYPE', 'VSUXSEGTYPE', 'VSOXSEGTYPE', 'VLRETYPE', 'VSRETYPE', 'VMTYPE', 'ZBS_IOP', 'ZBS_RTYPE', 'RISCV_JALR', 'RISCV_XPERM8', 'RISCV_XPERM4', 'F_BIN_RM_TYPE_H', 'F_MADD_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_BIN_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_RM_TYPE_H', 'F_UN_TYPE_H', 'F_UN_TYPE_H', 'F_UN_TYPE_H', 'SHA256SIG0', 'SHA256SIG1', 'SHA256SUM0', 'SHA256SUM1', 'AES32ESMI', 'AES32ESI', 'AES32DSMI', 'AES32DSI', 'SHA512SIG0H', 'SHA512SIG0L', 'SHA512SIG1H', 'SHA512SIG1L', 'SHA512SUM0R', 'SHA512SUM1R', 'AES64KS1I', 'AES64KS2', 'AES64IM', 'AES64ESM', 'AES64ES', 'AES64DSM', 'AES64DS', 'SHA512SIG0', 'SHA512SIG1', 'SHA512SUM0', 'SHA512SUM1', 'RISCV_JALR', 'C_ADDI4SPN', 'C_LW', 'C_LD', 'C_SW', 'C_SD', 'C_ADDI', 'C_LI', 'C_ADDI16SP', 'C_LUI', 'C_SRLI', 'C_SRAI', 'C_ANDI', 'C_SUB', 'C_XOR', 'C_OR', 'C_AND', 'C_SUBW', 'C_ADDW', 'C_LWSP', 'C_LDSP', 'C_SWSP', 'C_SDSP', 'LOAD_FP', 'STORE_FP', 'F_MADD_TYPE_S', 'F_BIN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_UN_RM_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_BIN_TYPE_S', 'F_UN_TYPE_S', 'F_UN_TYPE_S', 'F_UN_TYPE_S', 'RIVVTYPE', 'RMVVTYPE', 'RFVVTYPE', 'C_FLWSP', 'C_FSWSP', 'C_FLW', 'C_FSW', 'RISCV_SLLIUW', 'ZBA_RTYPEUW', 'ZBA_RTYPE', 'F_MADD_TYPE_D', 'F_BIN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_UN_RM_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_BIN_TYPE_D', 'F_UN_TYPE_D', 'F_UN_TYPE_D', 'F_UN_TYPE_D', 'LOADRES', 'STORECON', 'AMO', 'RISCV_CLMUL', 'RISCV_CLMULH', 'RISCV_CLMULR', 'ZBKB_RTYPE', 'ZBKB_PACKW', 'RISCV_ZIP', 'RISCV_UNZIP', 'RISCV_BREV8', 'MUL', 'DIV', 'REM', 'MULW', 'DIVW', 'REMW', 'URET', 'RISCV_RORIW', 'RISCV_RORI', 'ZBB_RTYPEW', 'ZBB_RTYPE', 'ZBB_EXTOP', 'RISCV_REV8', 'RISCV_ORCB', 'RISCV_CPOP', 'RISCV_CPOPW', 'RISCV_CLZ', 'RISCV_CLZW', 'RISCV_CTZ', 'RISCV_CTZW', 'ZICOND_RTYPE', 'ZICOND_RTYPE', 'VVMTYPE', 'VVMCTYPE', 'VVMSTYPE', 'VVCMPTYPE', 'VXMTYPE', 'VXMCTYPE', 'VXMSTYPE', 'VXCMPTYPE', 'VIMTYPE', 'VIMCTYPE', 'VIMSTYPE', 'VICMPTYPE', 'FVVMTYPE', 'FVFMTYPE', 'MMTYPE', 'VCPOP_M', 'VFIRST_M', 'VMSBF_M', 'VMSIF_M', 'VMSOF_M', 'VIOTA_M', 'VID_V', 'C_FLDSP', 'C_FSDSP', 'C_FLD', 'C_FSD', 'HFENCE_VVMA', 'HFENCE_GVMA', 'RISCV_FLI_H', 'RISCV_FLI_S', 'RISCV_FLI_D', 'RISCV_FMINM_H', 'RISCV_FMAXM_H', 'RISCV_FMINM_S', 'RISCV_FMAXM_S', 'RISCV_FMINM_D', 'RISCV_FMAXM_D', 'RISCV_FROUND_H', 'RISCV_FROUNDNX_H', 'RISCV_FROUND_S', 'RISCV_FROUNDNX_S', 'RISCV_FROUND_D', 'RISCV_FROUNDNX_D', 'RISCV_FMVH_X_D', 'RISCV_FMVP_D_X', 'RISCV_FLEQ_H', 'RISCV_FLTQ_H', 'RISCV_FLEQ_S', 'RISCV_FLTQ_S', 'RISCV_FLEQ_D', 'RISCV_FLTQ_D', 'RISCV_FCVTMOD_W_D', 'VSET_TYPE', 'VSETI_TYPE', 'SM3P0', 'SM3P1', 'SM4ED', 'SM4KS', 'VVTYPE', 'NVSTYPE', 'NVTYPE', 'MASKTYPEV', 'MOVETYPEV', 'VXTYPE', 'NXSTYPE', 'NXTYPE', 'VXSG', 'MASKTYPEX', 'MOVETYPEX', 'VITYPE', 'NISTYPE', 'NITYPE', 'VISG', 'MASKTYPEI', 'MOVETYPEI', 'VMVRTYPE', 'MVVTYPE', 'MVVMATYPE', 'WVVTYPE', 'WVTYPE', 'WMVVTYPE', 'VEXT2TYPE', 'VEXT4TYPE', 'VEXT8TYPE', 'VMVXS', 'MVVCOMPRESS', 'MVXTYPE', 'MVXMATYPE', 'WVXTYPE', 'WXTYPE', 'WMVXTYPE', 'VMVSX', 'FVVTYPE', 'FVVMATYPE', 'FWVVTYPE', 'FWVVMATYPE', 'FWVTYPE', 'VFUNARY0', 'VFWUNARY0', 'VFNUNARY0', 'VFUNARY1', 'VFMVFS', 'FVFTYPE', 'FVFMATYPE', 'FWVFTYPE', 'FWVFMATYPE', 'FWFTYPE', 'VFMERGE', 'VFMV', 'VFMVSF');
# instruction_definition_start = Str("function clause execute") + Str("", " ", "(", " (", "( ", " ( ");
# instruction_definition = instruction_definition_start + all_instruction_names;


# ----------------------------------------------------- Regex definitions ------------------------------------------------------------------ #

#match_privilege_mode_clause = Str("match") + Rep(AnyBut('{')) + Str("{") + Str(*arch_mode_names) + Rep(Str(""," ")) + Str("=>"); 
#+ Rep(AnyBut('}')) + Str("{");

match_priv_mode_clause = Str("match") + Rep(Str(""," ")) + Str("(", "", " ") + Str(*priv_level_symbol) + Rep(AnyBut("{")) + Str("{");
if_lhs_priv_mode_clause = Str("if") + Rep(Str(""," ")) + Str("(", "", " ") + Str(*priv_level_symbol) + Rep(Str(""," ")) + Str("==","!=") + Rep(Str(""," ")) + Str(*arch_priv_mode_names) + Rep(AnyBut("{")) + Str("then") + Rep(AnyBut("}")) + Str("}"); 
if_rhs_priv_mode_clause = Str("if") + Rep(Str(""," ")) + Str("(", "", " ") + Str(*arch_priv_mode_names) + Rep(Str(""," ")) + Str("==","!=") + Rep(Str(""," ")) + Str(*priv_level_symbol) + Rep(AnyBut("{")) + Str("then") + Rep(AnyBut("}")) + Str("}");  

# Entire match clause will get captured over here! 
match_priv_mode_case_1 = Str(*arch_priv_mode_names) + Rep(Str(""," ")) + Str("=>") + Rep(AnyBut(",}")) + Str(",", "};"); 
match_priv_mode_case_2 = Str(*arch_priv_mode_names) + Rep(Str(""," ")) + Str("=>") + Rep(Str(""," ")) + Str("{");

# ----------------------------------------------------- RISC-V Sail Scanner ---------------------------------------------------------------- #

# To capture instruction execution access per privilege level. 

class RISCV_Sail_Scanner(Scanner):
    definition_to_scan = instruction_definition; 

    def reached_definition(self, text): 
        self.reached_instruction_definition(text);

    def reached_instruction_definition(self, text): 
        global current_instruction_being_scanned;
        global scanning_instruction_definition;
        global scanning_function_definition;
        global scanning_instruction_definition;
        print("\n\n******************* Reached instruction definition: "+text+" *******************\n\n");
        if "execute(" in text:             
            current_instruction_being_scanned = text.split("execute(")[1].replace(" ","");
        elif "execute (" in text: 
            current_instruction_being_scanned = text.split("execute (")[1].replace(" ","");
        else: 
            current_instruction_being_scanned = text.split("execute")[1].replace(" ","");
        
        # By the end of the instruction definition scanning, it should be updated.
        instruction_executable[0][current_instruction_being_scanned] = "Default";
        instruction_executable[1][current_instruction_being_scanned] = "Default";
        instruction_executable[2][current_instruction_being_scanned] = "Default";
        instruction_executable[3][current_instruction_being_scanned] = "Default";
        instruction_executable[4][current_instruction_being_scanned] = "Default";
        
        scanning_instruction_definition = True; 
        self.begin('scanning_definition');


    def begin_comment_in_default_state(self, text):
        global previous_scanner_state;
        previous_scanner_state = '';
        self.begin('inside_comment');

    def begin_comment_while_scanning_definition(self, text): 
        global previous_scanner_state;
        previous_scanner_state = 'scanning_definition';
        self.begin('inside_comment');

    def restore_previous_state(self, text):
        global previous_scanner_state;
        self.begin(previous_scanner_state);

    def done_scanning_definition(self, text): 
        global current_instruction_being_scanned;
        global scanning_instruction_definition;
        print("\n\n********************\ Completed scanning definition ********************\n\n");
        current_instruction_being_scanned = "";
        scanning_instruction_definition = False; 
        # TODO: If all "Default", update all to "TRUE".
        self.begin('');

    def found_match_priv_mode(self, text):
        if "{" in text: 
            braces_to_match.append("{"); 
        print("\n Found match case: "+text);
        self.begin('match_priv_mode'); 

    def found_if_priv_mode(self, text): 
        print("Found if priv mode: "+text);
        # TODO: Just use find... Not so imp! 
        priv_mode_index = -1;
        i = 0;
        for mode in arch_priv_mode_names: 
            if mode in text: 
                #priv_mode_of_case = mode; 
                priv_mode_index = i;
                break; 
            i = i + 1;

        if priv_mode_index == 5:
            priv_mode_index = 4; 

        exec_fail = False;
        exec_success = False; 
        comparator = "";
    
        if "==" in text: 
            comparator = "==";
        elif "!=" in text: 
            comparator = "!=";
    
        for succ in instr_exec_success: 
            if succ in text: 
                exec_success = True; 

        for fail in instr_exec_fail: 
            if fail in text: 
                exec_fail = True; 

        print("Found: "+comparator+" ");

        # E.g. If != machine then fail. so != means assign all else, == means, assign just that one. 
        if exec_fail == False and exec_success == False: 
            # NOT ABLE TO DETERMINE!  
            if comparator == "==": 
                instruction_executable[priv_mode_index][current_instruction_being_scanned] = "Undefined";
            elif comparator == "!=": 
                i = 0;
                for mode in arch_priv_mode_names: 
                    if i != priv_mode_index: 
                        instruction_executable[i][current_instruction_being_scanned] = "Undefined";
                    i = i + 1;
                    if i == 5: 
                        break;
        elif exec_fail == True and exec_success == True: 
            if comparator == "==": 
                # Conditional successful execution? 
                instruction_executable[priv_mode_index][current_instruction_being_scanned] = "TRUE/FALSE";
            elif comparator == "!=": 
                # This case is not so likely I expect... 
                i = 0;
                for mode in arch_priv_mode_names: 
                    if i != priv_mode_index: 
                        instruction_executable[i][current_instruction_being_scanned] = "TRUE/FALSE";
                    i = i + 1;
                    if i == 5: 
                        break;
        elif exec_success == True: 
            if comparator == "==": 
                instruction_executable[priv_mode_index][current_instruction_being_scanned] = "TRUE";
            elif comparator == "!=": 
                i = 0;
                for mode in arch_priv_mode_names: 
                    if i != priv_mode_index: 
                        instruction_executable[i][current_instruction_being_scanned] = "TRUE";
                    else: 
                        instruction_executable[i][current_instruction_being_scanned] = "FALSE";
                    i = i + 1;
                    if i == 5: 
                        break;
        elif exec_fail == True: 
            if comparator == "==": 
                instruction_executable[priv_mode_index][current_instruction_being_scanned] = "FALSE";
            elif comparator == "!=": 
                print("Comparator !=");
                i = 0;
                for mode in arch_priv_mode_names: 
                    if i != priv_mode_index: 
                        instruction_executable[i][current_instruction_being_scanned] = "FALSE";
                    else: 
                        instruction_executable[i][current_instruction_being_scanned] = "TRUE";
                    i = i + 1;
                    if i == 5: 
                        break;


    #def found_if_rhs_priv_mode(self, text): 

    def found_match_priv_mode_case(self, text): 
        print("Found match priv mode case: "+text);
        #priv_mode_of_case = "";
        priv_mode_index = -1;
        exec_fail = False;
        exec_success = False; 
    
        # TODO: Just use find... Not so imp! 
        i = 0;
        for mode in arch_priv_mode_names: 
            if mode in text: 
                #priv_mode_of_case = mode; 
                priv_mode_index = i;
                break; 
            i = i + 1;

        if priv_mode_index == 5:
            priv_mode_index = 4; 

        for succ in instr_exec_success: 
            if succ in text: 
                exec_success = True; 

        for fail in instr_exec_fail: 
            if fail in text: 
                exec_fail = True; 

        if exec_fail == False and exec_success == False: 
            # NOT ABLE TO DETERMINE!  
            instruction_executable[priv_mode_index][current_instruction_being_scanned] = "Undefined";
        elif exec_fail == True and exec_success == True: 
            # Conditional successful execution? 
            instruction_executable[priv_mode_index][current_instruction_being_scanned] = "TRUE/FALSE";
        elif exec_success == True: 
            instruction_executable[priv_mode_index][current_instruction_being_scanned] = "TRUE";
        elif exec_fail == True: 
            instruction_executable[priv_mode_index][current_instruction_being_scanned] = "FALSE";

    def found_second_match_priv_mode_case(self, text): 
        print("Found match priv mode case: "+text);
        #priv_mode_of_case = "";
        priv_mode_index = -1;
    
        # TODO: Just use find... Not so imp! 
        i = 0;
        for mode in arch_priv_mode_names: 
            if mode in text: 
                #priv_mode_of_case = mode; 
                priv_mode_index = i;
                break; 
            i = i + 1;
    
        if priv_mode_index == 5:
            priv_mode_index = 4; 

        # It might not be worth it to keep scanning within the match case using the scanner. Such cases are very low, and highly dependent on code quality.
        # Atm, we just assign "Undefined". 
        instruction_executable[priv_mode_index][current_instruction_being_scanned] = "Undefined";

    def done_scanning_match_clause(self, text):
        print("Done scanning match clause.");
        self.begin('scanning_definition');

    def exit_analysis(self, text): 
        print("Exiting analysis");
        exit(0);

    def __init__(self, file, name):
        Scanner.__init__(self, self.lexicon, file, name);
        
        # arch_module_name = "";
        # if arch == "riscv64":
        #     arch_module_name = "riscv";
        # elif arch == "riscv64-hext":
        #     arch_module_name = "riscv_h";
        # elif arch == "arm":
        #     arch_module_name = "arm";
    
        # try:
        #     self.arch_module = import_module(arch_module_name);
        # except ImportError:
        #     print(f"Unsupported architecture: {arch}");
        #     exit(0);

    lexicon = Lexicon([
        (definition_to_scan, reached_definition), 
        (Rep1(Any(" \t\n")),    IGNORE),
        (name,                  IGNORE),
        (small_comment,         IGNORE),
        (Str("/*"),             begin_comment_in_default_state),
        (AnyChar,               IGNORE),
        State('scanning_definition', [
            (Rep1(Any(" \t\n")),    IGNORE),
            (definition_to_scan, reached_definition),
            (keywords_of_interest,  done_scanning_definition), 
            (match_priv_mode_clause, found_match_priv_mode),
            (if_lhs_priv_mode_clause, found_if_priv_mode),
            (if_rhs_priv_mode_clause, found_if_priv_mode),
            # If clause 
            # Else clause 
            # Match clause 

            #(arch_module.function_call,         IGNORE),
            # (arch_module.csr_read_and_write_instance, found_csr_read_plus_write_instance),
            # #(arch_module.csr_read_if_clause_1 | arch_module.csr_read_if_clause_2 | arch_module.csr_read_match_clause | arch_module.csr_read_for_comparison_rhs | arch_module.csr_read_for_comparison_lhs | arch_module.csr_read_instance_1,  found_csr_read),
            # (arch_module.csr_read_if_clause_1, found_csr_read),
            # (arch_module.csr_read_if_clause_2, found_csr_read),
            # (arch_module.csr_read_match_clause, found_csr_read),
            # (arch_module.csr_read_for_comparison_rhs, found_csr_read),
            # (arch_module.csr_read_for_comparison_lhs, found_csr_read),
            # (arch_module.csr_read_instance_1, found_csr_read),
            # (arch_module.csr_write_instance_1,  found_csr_write),
            # (Str(*arch_module.ctrl_reg_names),              found_csr_use),
            (print_reg_pattern,     IGNORE),
            (name,                  IGNORE),
            (Str("/*"),             begin_comment_while_scanning_definition),
            (AnyChar,               IGNORE),
            (small_comment,        IGNORE),
        ]),
        State('inside_comment', [ 
            (Str("*/"),         restore_previous_state),
            (AnyChar,           IGNORE)
        ]),
        State('match_priv_mode', [
            (match_priv_mode_case_1,  found_match_priv_mode_case),
            (match_priv_mode_case_2,  found_second_match_priv_mode_case),
            (Str("}"),      done_scanning_match_clause),
            (AnyChar,           IGNORE),
        ])
    ])
