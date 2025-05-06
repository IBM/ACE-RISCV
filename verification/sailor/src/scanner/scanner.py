# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# -------------- The aim of this module is to scan Sail code to extract information about CSR use on executing RISC-V instructions ----------------------- #
# -------------- This file just initializes a new SailScanner for all the files to scan and scans them token by token (by using Plex) ------------------ #
# -------------- The SailScanner is an extension of the Plex Scanner and is defined in the sail_lexer module ------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #

import csv;
import sys;
from riscv import *;
from importlib import import_module, invalidate_caches, reload;

sail_dir = "";
sail_model_dir = "";
results_dir = "";
arch_module = "";
arch_name = "";
arch_module_name = "";

def scan_definition(files_to_scan, scanner_definition): 
    try:
        lexer_mod = import_module("scanner.lexer");
    except ImportError:
        print(f"Unable to import SailorScanner lexer module");
        exit(0);
   
    for file_name in files_to_scan:
        #for file_name in files_to_scan_for_func_defs:
        print("Scanning "+file_name);
        f = open(file_name, 'r');
        scanner = lexer_mod.SailScanner(f, file_name, scanner_definition, arch_name);
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

def process_function_ctrl_reg_footprint():
    try:
        lexer_mod = import_module("scanner.lexer");
    except ImportError:
        print(f"Unable to import SailorScanner lexer module..");
        exit(0);
    
    # First, complete the CSR footprint of functions by adding the CSR footprints of the functions which are in the footprint of the function. (Twister, but it makes sense.)
    for fn in lexer_mod.function_footprint_of_function.keys():
        for fn_name in lexer_mod.function_footprint_of_function[fn]: 
            if len(lexer_mod.CSR_footprint_of_function[fn_name]) > 0: 
                for csr in lexer_mod.CSR_footprint_of_function[fn_name]: 
                    if csr not in lexer_mod.CSR_footprint_of_function[fn]: 
                        lexer_mod.CSR_footprint_of_function[fn].append(csr);

    # Second, if CSR, CSR Read, and CSR Write in the CSR footprint, then remove CSR. 
    for fn in lexer_mod.CSR_footprint_of_function.keys(): 
        for csr in arch_module.ctrl_reg_names: 
            if csr in lexer_mod.CSR_footprint_of_function[fn] and csr+" Read" in lexer_mod.CSR_footprint_of_function[fn] and csr+" Write" in lexer_mod.CSR_footprint_of_function[fn]:
                lexer_mod.CSR_footprint_of_function[fn].remove(csr);

    # Third, if CSR Read and CSR Write in the footprint: call it CSR R+W. 
    for fn in lexer_mod.CSR_footprint_of_function.keys(): 
        for csr in arch_module.ctrl_reg_names: 
            if csr+" Read" in lexer_mod.CSR_footprint_of_function[fn] and csr+" Write" in lexer_mod.CSR_footprint_of_function[fn]:
                lexer_mod.CSR_footprint_of_function[fn].remove(csr+" Read");
                lexer_mod.CSR_footprint_of_function[fn].remove(csr+" Write");
                lexer_mod.CSR_footprint_of_function[fn].append(csr+" R+W");

    print("Printing function footprints:");
    print("\n\n");
    for key, value in lexer_mod.CSR_footprint_of_function.items():
       print(f"{key}: {value}")

    print("\n\n");

    for key, value in lexer_mod.function_footprint_of_function.items():
     print(f"{key}: {value}")

    print("\n\n");

    # for fn in lexer_mod.CSR_footprint_of_function.keys(): 
    #     for csr_use in lexer_mod.CSR_footprint_of_function[fn]: 
    #         if "Read" in csr_use: 
    #             csr_uses_reads = csr_uses_reads + 1;
    #         elif "Write" in csr_use: 
    #             csr_uses_writes = csr_uses_writes + 1;
    #         elif "R+W" in csr_use: 
    #             csr_uses_reads = csr_uses_reads + 1;
    #             csr_uses_writes = csr_uses_writes + 1;
    #         else: 
    #             csr_uses_not_decoded = csr_uses_not_decoded + 1;

    print("CSR_uses_reads: "+str(lexer_mod.csr_uses_reads));
    print("CSR_uses_writes: "+str(lexer_mod.csr_uses_writes));
    print("CSR_uses_not_decoded: "+str(lexer_mod.csr_uses_not_decoded));

    print("\n\n");
    print(lexer_mod.CSR_footprint_of_function);
    print("\n\n"); 

# ------------------------------------------------ A little post-processing for instruction analysis --------------------------------------------------------- #
def process_instruction_ctrl_reg_footprint():
    try:
        lexer_mod = import_module("scanner.lexer");
    except ImportError:
        print(f"Unable to import SailorScanner lexer module.");
        exit(0);
    
    # Pre-first, add step to the function footprint of each instruction. 
    for instr in lexer_mod.function_footprint_of_instruction.keys():
        lexer_mod.function_footprint_of_instruction[instr].append('step');

    # First, complete the CSR footprint of instructions by adding the CSR footprints of the functions which are in the footprint of the instruction. (Twister, but it makes sense.)
    for instr in lexer_mod.function_footprint_of_instruction.keys():
        for fn_name in lexer_mod.function_footprint_of_instruction[instr]: 
            if fn_name in lexer_mod.CSR_footprint_of_function.keys():
                if len(lexer_mod.CSR_footprint_of_function[fn_name]) > 0: 
                    for csr in lexer_mod.CSR_footprint_of_function[fn_name]: 
                        if csr not in lexer_mod.CSR_footprint_of_instruction[instr]: 
                            lexer_mod.CSR_footprint_of_instruction[instr].append(csr);

    # Second, if CSR, CSR Read, and CSR Write in the CSR footprint, then remove CSR. 
    for instr in lexer_mod.CSR_footprint_of_instruction.keys(): 
        for csr in arch_module.ctrl_reg_names: 
            if csr in lexer_mod.CSR_footprint_of_instruction[instr] and csr+" Read" in lexer_mod.CSR_footprint_of_instruction[instr] and csr+" Write" in lexer_mod.CSR_footprint_of_instruction[instr]:
                lexer_mod.CSR_footprint_of_instruction[instr].remove(csr);

    # Third, if CSR Read and CSR Write in the footprint: call it CSR R+W. 
    for instr in lexer_mod.CSR_footprint_of_instruction.keys(): 
        for csr in arch_module.ctrl_reg_names: 
            if csr+" Read" in lexer_mod.CSR_footprint_of_instruction[instr] and csr+" Write" in lexer_mod.CSR_footprint_of_instruction[instr]:
                lexer_mod.CSR_footprint_of_instruction[instr].remove(csr+" Read");
                lexer_mod.CSR_footprint_of_instruction[instr].remove(csr+" Write");
                lexer_mod.CSR_footprint_of_instruction[instr].append(csr+" R+W");

    # for instr in lexer_mod.CSR_footprint_of_instruction.keys(): 
    #     for csr_use in lexer_mod.CSR_footprint_of_instruction[instr]: 
    #         if "Read" in csr_use: 
    #             csr_uses_reads = csr_uses_reads + 1;
    #         elif "Write" in csr_use: 
    #             csr_uses_writes = csr_uses_writes + 1;
    #         elif "R+W" in csr_use: 
    #             csr_uses_reads = csr_uses_reads + 1;
    #             csr_uses_writes = csr_uses_writes + 1;
    #         else: 
    #             csr_uses_not_decoded = csr_uses_not_decoded + 1;

    print("CSR_uses_reads: "+str(lexer_mod.csr_uses_reads));
    print("CSR_uses_writes: "+str(lexer_mod.csr_uses_writes));
    print("CSR_uses_not_decoded: "+str(lexer_mod.csr_uses_not_decoded));

    print("\n\n");

    for key, value in lexer_mod.function_footprint_of_instruction.items():
        print(f"{key}: {value}")

    print("\n\n");
    for key, value in lexer_mod.CSR_footprint_of_instruction.items():
        print(f"{key}: {value}")

    print("\n\n");

def dict_to_csv(data, output_file):
  """Converts a dictionary with list values to a CSV file.
  Args:
    data: The dictionary to convert.
    output_file: The name of the output CSV file.
  """
  # Find maximum list length
  max_len = max(len(v) for v in data.values())

  # Create a list of lists with padded values
  rows = []
  for key, value in data.items():
      row = [key] + value + [''] * (max_len - len(value))
      rows.append(row)

  # Write to CSV
  with open(output_file, 'w', newline='') as csvfile:
      writer = csv.writer(csvfile)
      writer.writerows(rows)

def compute_ctrl_reg_footprint(): 
    global results_dir;
    print("Scanning all defs...");
    scan_definition(list(set(arch_module.files_to_scan_for_func_defs) | set(arch_module.files_to_scan_for_instr_defs)), arch_module.function_definition);
    process_function_ctrl_reg_footprint();
    process_instruction_ctrl_reg_footprint();

    # Scan the Sail model for all function definitions
    # print("Scanning function defs...");
    # scan_definition(arch_module.files_to_scan_for_func_defs, arch_module.function_definition);
    # process_function_ctrl_reg_footprint();

    # invalidate_caches();
    # print("Scanning instruction defs...");
    # # Scan the Sail model for all instruction definitions
    # scan_definition(arch_module.files_to_scan_for_instr_defs, arch_module.instruction_definition);
    # process_instruction_ctrl_reg_footprint();
    
    # Scan the Sail model for interrupt control, memory management control, and performance monitoring unit.
    # Note: Other defs are just functions. We will not repeat a scan if info is already extracted while scanning function defintions.
    # scan_definition(arch_module.files_to_scan_for_other_defs, arch_module.other_defs);
    # process_other_def_footprint();

    # In this step, we add all "other defs" footprints to all instructions since interrupts can be serviced before/after execution of all instructions, PMU is updated after execution of all instructions, and all instructions are fetched from memory before being issued into the pipeline.
    #add_other_def_footprint_to_instructions();
    try:
        lexer_mod = import_module("scanner.lexer");
    except ImportError:
        print(f"Unable to import SailorScanner lexer module!");
        exit(0);
    
    dict_to_csv(lexer_mod.CSR_footprint_of_instruction, results_dir+"/scanner-results/"+arch_name+"/csr-footprint-per-instruction.csv");

    
def main(argv_arch, argv_sail_dir, argv_sail_model_dir, argv_results_dir): 
    global sail_model_dir;
    global arch_module;
    global arch_name;
    global results_dir;

    # if len(sys.argv) != 3: 
    #     print("Please provide architecture and Sail model directory as command line arguments.");
    #     exit(0);

    arch_module_name = "";
    #arch_name = sys.argv[1];
    arch_name = argv_arch;
    if arch_name == "riscv64":
        arch_module_name = "riscv";
    elif arch_name == "riscv64-hext":
        arch_module_name = "riscv_h";
    elif arch_name == "arm":
        arch_module_name = "arm";
    else: 
        print("Error! Unsupported architecture!");
        exit(0);
    
    try:
        arch_module = import_module(arch_module_name);
    except ImportError:
        print(f"Unsupported architecture: {sys.argv[1]}");
        exit(0);

    #sail_model_dir = sys.argv[2];
    sail_dir = argv_sail_dir;
    sail_model_dir = argv_sail_model_dir;
    results_dir = argv_results_dir;

    os.popen('mkdir -p '+results_dir);
    os.popen('mkdir -p '+results_dir+'/scanner-results');
    os.popen('mkdir -p '+results_dir+'/scanner-results/'+arch_name);

    # Step 1: Architectural init. Extract CSR names, instruction names, function names, etc. 
    arch_module.arch_init(sail_dir, sail_model_dir, results_dir); 
    
    # Step 2: Ask Sail which csrs are accessible by which privilege modes.      
    arch_module.arch_ctrl_reg_access();

    # Step 3: Ask Sail which instructions are executable by which privilege modes.    
    # TODO: Need to rewrite with Plex! 
    arch_module.arch_instr_access();

    # Step 4: Compute CSR footprint 
    compute_ctrl_reg_footprint();





