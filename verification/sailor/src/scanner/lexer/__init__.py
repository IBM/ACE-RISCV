# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# -------------- This file defines a SailScanner class (an extension of the Scanner from the Plex (Python lexical analysis) library -------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #

from plex import *;
from sail_syntax import *;
from riscv import *;
from importlib import *;
#from scanner_config import *;

# ------------------------------------------------ Basic regex for words/names, comments, spaces --------------------------------------------------------- #

letter = Range("AZaz");
digit = Range("09");
underscore = Str("_");
open_square_bracket = Str("[");
close_square_bracket = Str("]");
name = letter + Rep(letter | digit | underscore | open_square_bracket | close_square_bracket);

open_parenthesis = Str("(");
close_parenthesis = Str(")");

# neeluk: We don't expect nested comments. If they exist in the Sail code, the analysis results might gather some noise. 
small_comment = Str("//") + Rep(AnyBut("\n")) + Str("\n");
space = Any(" \t\n");
string_arg = Str('"') + Rep(AnyBut('"')) + Str('"');

# ----------------------------------------------------- Intermediate state tracking ---------------------------------------------------------------------- #

current_instruction_being_scanned = "";
current_function_being_scanned = "";
scanning_instruction_definition = False; 
scanning_function_definition = False; 
previous_scanner_state = '';    # This is the default state anyway..... 
parenthesis_to_match = [];

# definition_to_scan = "";

# --------------------------------------------------------- Output of the analysis ---------------------------------------------------------------------- #

CSR_footprint_of_instruction = {};
function_footprint_of_instruction = {};

CSR_footprint_of_function = {};
function_footprint_of_function = {};

#CSR_footprint_of_augmented_function = {};
#function_footprint_of_augmented_function = {};

# Some statistics 

csr_uses_not_decoded = 0; 
csr_uses_reads = 0; 
csr_uses_writes = 0; 

# TODO: Decode all the not decoded CSR uses and add more rules if necessary! (There are only ~34 undecoded). (As opposed to, reads decoded which are like 640 and writes which are 255!).

# ----------------------------------------------------- Sailor Scanner ---------------------------------------------------------------- #

class SailScanner(Scanner):
    definition_to_scan = function_definition | instruction_definition;    # Needs to be initialized while creating the scanner. 
    arch_module = import_module("riscv");              # Default to RISC-V? 

    def reached_definition(self, text): 
        if "execute" in text:
            self.reached_instruction_definition(text);
        else: 
            self.reached_function_definition(text);

    def reached_instruction_definition(self, text): 
        global current_instruction_being_scanned;
        global scanning_instruction_definition;
        global CSR_footprint_of_instruction;
        global function_footprint_of_instruction;
        global scanning_function_definition;
        global scanning_instruction_definition;
        print("\n\n******************* Reached instruction definition: "+text+" *******************\n\n");
        if "execute(" in text:             
            current_instruction_being_scanned = text.split("execute(")[1].replace(" ","");
        elif "execute (" in text: 
            current_instruction_being_scanned = text.split("execute (")[1].replace(" ","");
        else: 
            current_instruction_being_scanned = text.split("execute")[1].replace(" ","");
        CSR_footprint_of_instruction[current_instruction_being_scanned] = [];
        function_footprint_of_instruction[current_instruction_being_scanned] = [];
        scanning_instruction_definition = True; 
        if scanning_function_definition == True: 
            scanning_function_definition = False;
            current_function_being_scanned = "";
        self.begin('scanning_definition');

    def reached_function_definition(self, text): 
        global current_function_being_scanned;
        global scanning_function_definition;
        global CSR_footprint_of_function;
        global function_footprint_of_function;
        global scanning_instruction_definition;
        global current_instruction_being_scanned;
        print("\n\n******************* Reached function definition: "+text+" *******************\n\n");
        current_function_being_scanned = text.split("function")[1].replace(" ","");
        CSR_footprint_of_function[current_function_being_scanned] = [];
        function_footprint_of_function[current_function_being_scanned] = [];
        scanning_function_definition = True; 
        if scanning_instruction_definition == True:
            scanning_instruction_definition = False;
            current_instruction_being_scanned = "";
        self.begin('scanning_definition');

    def found_function_call(self, text): 
        global scanning_instruction_definition;
        global scanning_function_definition;
        print("Found function call: "+text);
        fn_name = text.split("(")[0].replace(" ","");
        
        if scanning_instruction_definition and scanning_function_definition: 
            print("Scanning instruction and function definition simultaneously!!!");
            exit(0);
        if scanning_instruction_definition: 
            if fn_name not in functions_to_ignore and fn_name not in function_footprint_of_instruction[current_instruction_being_scanned]:
                function_footprint_of_instruction[current_instruction_being_scanned].append(fn_name);
        elif scanning_function_definition: 
            if fn_name not in functions_to_ignore and fn_name not in function_footprint_of_function[current_function_being_scanned]:
                function_footprint_of_function[current_function_being_scanned].append(fn_name);
        else: 
            print("Scanning neither instruction nor function definition!!!");
            exit(0);
        
        global parenthesis_to_match;
        if len(parenthesis_to_match) > 0: 
            print("parenthesis_to_match length is greater than 0 on a new function call");
            exit(0);
        parenthesis_to_match.append("(");
        self.begin('scanning_function_call_args');

    def open_paren(self, text):
        global parenthesis_to_match;
        parenthesis_to_match.append("(");
        print("Found opening parenthesis: "+text);
        print(parenthesis_to_match);
    
    def nested_function_call(self, text):
        global parenthesis_to_match;
        global scanning_instruction_definition;
        global scanning_function_definition;
        self.open_paren(text);
        # TODO: Add in function footprint of function.  
        fn_name = text.split("(")[0].replace(" ","");
        print("Nested function call: "+text);
        if scanning_instruction_definition and scanning_function_definition: 
            print("Scanning instruction and function definition simultaneously!!!");
            exit(0);
        if scanning_instruction_definition: 
            if fn_name not in functions_to_ignore and fn_name not in function_footprint_of_instruction[current_instruction_being_scanned]:
                function_footprint_of_instruction[current_instruction_being_scanned].append(fn_name);
        elif scanning_function_definition: 
            if fn_name not in functions_to_ignore and fn_name not in function_footprint_of_function[current_function_being_scanned]:
                function_footprint_of_function[current_function_being_scanned].append(fn_name);
        else: 
            print("Scanning neither instruction nor function definition!!!");
            exit(0);
        # parenthesis_to_match.append('('); # This was an extra append.. caused problems. 
        # We will not nest the 'scanning_function_call_args' state in the Scanner.... that's not possible to do in Plex, and it could lead to undefined states, unmanageable nesting depth, other bugs. 
        # But all args to the nested function call will still be scanned and reported as args to the outermost function call. 

    def close_paren(self,text):
        global parenthesis_to_match;
        parenthesis_to_match.pop();
        print("found closing paren: "+text);
        print(parenthesis_to_match);
        if len(parenthesis_to_match) == 0:
            print("Done analysing function args");
            self.begin('scanning_definition');  #Go back to scanning definition.

    def found_name(self, text): 
        print("Found name: "+text);
        #print("Name: "+text);

    def found_char(self, text): 
        print("Found char: "+text)
        #print("Char: "+text);

    def found_csr_use(self, text):
        global csr_uses_not_decoded;
        global scanning_instruction_definition;
        global scanning_function_definition;
        csr_uses_not_decoded = csr_uses_not_decoded + 1;
        print("Found CSR use: "+text);
        if scanning_instruction_definition and scanning_function_definition: 
            print("Scanning instruction and function definition simultaneously!!!");
            exit(0);
        if scanning_instruction_definition: 
            if text not in CSR_footprint_of_instruction[current_instruction_being_scanned]:
                CSR_footprint_of_instruction[current_instruction_being_scanned].append(text); 
        elif scanning_function_definition: 
            if text not in CSR_footprint_of_function[current_function_being_scanned]:
                CSR_footprint_of_function[current_function_being_scanned].append(text);
        else: 
            print("Scanning neither instruction nor function definition!!!");
            exit(0);

    def found_csr_read(self, text): 
        global csr_uses_reads;
        global scanning_instruction_definition;
        global scanning_function_definition;
        csr_uses_reads = csr_uses_reads + 1; 
        print("Found CSR read: "+text);
        if scanning_instruction_definition and scanning_function_definition: 
            print("Scanning instruction and function definition simultaneously!!!");
            exit(0);
        for csr in self.arch_module.ctrl_reg_names: 
            if csr in text: 
                if scanning_instruction_definition: 
                    if csr+" Read" not in CSR_footprint_of_instruction[current_instruction_being_scanned]:
                        CSR_footprint_of_instruction[current_instruction_being_scanned].append(csr+" Read");
                        text.replace(csr, "");
                elif scanning_function_definition: 
                    if csr+" Read" not in CSR_footprint_of_function[current_function_being_scanned]:
                        CSR_footprint_of_function[current_function_being_scanned].append(csr+" Read");
                        text.replace(csr, "");
                else: 
                    print("Scanning neither instruction nor function definition!!!");
                    exit(0);

    def found_csr_write(self, text): 
        global csr_uses_writes;
        global scanning_instruction_definition;
        global scanning_function_definition;
        csr_uses_writes = csr_uses_writes + 1;
        print("Found CSR write: "+text);
        if scanning_instruction_definition and scanning_function_definition: 
            print("Scanning instruction and function definition simultaneously!!!");
            exit(0);
        for csr in self.arch_module.ctrl_reg_names: 
            if csr in text: 
                if scanning_instruction_definition: 
                    if csr+" Write" not in CSR_footprint_of_instruction[current_instruction_being_scanned]:
                        CSR_footprint_of_instruction[current_instruction_being_scanned].append(csr+" Write");
                elif scanning_function_definition: 
                    if csr+" Write" not in CSR_footprint_of_function[current_function_being_scanned]:
                        CSR_footprint_of_function[current_function_being_scanned].append(csr+" Write");
                else: 
                    print("Scanning neither instruction nor function definition!!!");
                    exit(0);
                break;
    
    def found_csr_read_plus_write_instance(self, text): 
        #print("Exiting analysis - Found both CSR Read and Write in one expression.");
        #print(text);
        #exit(0);
        print("Found CSR read + write: "+text);
        expr_tokens = text.split("=");
        if len(expr_tokens) != 2: 
            print("Exiting analysis - Found both CSR Read and Write in one expression.");
            print(text);
            exit(0);
        self.found_csr_write(expr_tokens[0]); # LHS 
        self.found_csr_read(expr_tokens[1]); # RHS 


    def found_keywords_of_interest_in_fn_call_args(self, text): 
        print("found_keywords_of_interest_in_fn_call_args: "+text);
        exit(0);

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
        global current_function_being_scanned;
        global scanning_function_definition;
        global scanning_instruction_definition;
        print("\n\n********************\ Completed scanning definition ********************\n\n");
        current_instruction_being_scanned = "";
        current_function_being_scanned = "";
        scanning_instruction_definition = False; 
        scanning_function_definition = False;
        self.begin('');

    def exit_analysis(self, text): 
        print("Exiting analysis");
        exit(0);

    def __init__(self, file, name, definition, arch):
        #global defintion_to_scan;
        # self.defintion_to_scan = definition; 
        # print("Definition to scan is:");
        # print(self.definition_to_scan);
        # print("Supplied definition: ");
        # print(definition);
        Scanner.__init__(self, self.lexicon, file, name);
        
        arch_module_name = "";
        if arch == "riscv64":
            arch_module_name = "riscv";
        elif arch == "riscv64-hext":
            arch_module_name = "riscv_h";
        elif arch == "arm":
            arch_module_name = "arm";
    
        try:
            self.arch_module = import_module(arch_module_name);
        except ImportError:
            print(f"Unsupported architecture: {arch}");
            exit(0);


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
            (arch_module.function_call,         found_function_call),
            (arch_module.csr_read_and_write_instance, found_csr_read_plus_write_instance),
            #(arch_module.csr_read_if_clause_1 | arch_module.csr_read_if_clause_2 | arch_module.csr_read_match_clause | arch_module.csr_read_for_comparison_rhs | arch_module.csr_read_for_comparison_lhs | arch_module.csr_read_instance_1,  found_csr_read),
            (arch_module.csr_read_if_clause_1, found_csr_read),
            (arch_module.csr_read_if_clause_2, found_csr_read),
            (arch_module.csr_read_match_clause, found_csr_read),
            (arch_module.csr_read_for_comparison_rhs, found_csr_read),
            (arch_module.csr_read_for_comparison_lhs, found_csr_read),
            (arch_module.csr_read_instance_1, found_csr_read),
            (arch_module.csr_write_instance_1,  found_csr_write),
            (Str(*arch_module.ctrl_reg_names),              found_csr_use),
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
        State('scanning_function_call_args', [ 
            (Str(","),      IGNORE),
            (arch_module.function_call, nested_function_call),
            # A pattern for '(' is added here because it might be that a fn_call() within the arguments is not in the function_names list. 
            # It will instead be recognized as a name, and treated as an argument. 
            # In that case, we still want an accurate parenthesis count. 
            (Str("("),      open_paren),   
            (Str(")"),      close_paren),
            (Str(*arch_module.ctrl_reg_names),      found_csr_read),
            (arch_module.instruction_definition, reached_instruction_definition), # TODO: Should this be allowed?
            #(function_definition,   reached_function_definition),
            (keywords_of_interest, found_keywords_of_interest_in_fn_call_args),
            (print_reg_pattern, IGNORE),
            (string_arg,        IGNORE),
            (name,          IGNORE),
            (Rep1(Any(" \t\n")),    IGNORE),
            (AnyChar,               IGNORE),
        ])
    ])