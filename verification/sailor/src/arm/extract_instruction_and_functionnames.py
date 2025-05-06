# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ------------------------------------- This file scans the Sail model of Arm for instruction defintions ----------------------------------------------- #
# ------------- It then extracts the names of all the instructions, for later use by Sailor (SailScanner) through the sail_syntax pkg ------------------ #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #


import os; 

sail_model_dir = "sail-arm/arm-v9.4-a/src/"

parenthesis_to_match = [];
braces_to_match = [];

function_names = [];
instruction_names = [];
register_names = [];
files_to_scan_for_func_defs = [];
files_to_scan_for_instr_defs = [];
files_to_scan_for_reg_defs = [];

def find_instruction_names():
    with os.popen('grep -nr "function execute_" '+sail_model_dir) as res: 
        for instr_def in res: 
            # Ensure there is a "= {" i.e. execute definition start, else ignore.  
            # Note: Several instructions end with "= RETIRE_SUCCESS" definitions. We ignore those. 
            # Note: Instructions implemented in the "cext" eventually call execute of other instructions which we are analysing. 
            # Note: These (cext) instructions do not use any privilege information explicitly, so analysing just the instruction's implementation they execute is enough (e.g. ebreak for c_ebreak). So, we ignore these. 
            # Note: The only exception which is excluded by the following condition is "WFI". We analyse that one manually. 
            # if "= {" not in instr_def: 
            #     continue;
        
            # if "handle_illegal" in instr_def or "execute CSR(" in instr_def: 
            #     continue;

            instr_def_split = instr_def.split(":");
            instr_file_name = instr_def_split[0];
            #instr_line_num = int(instr_def_split[1]);
            instr_name = instr_def_split[2].split("execute_")[1].split(" ")[0];

            print(instr_def);
            instruction_names.append(instr_name);
            if instr_file_name not in files_to_scan_for_instr_defs:
                files_to_scan_for_instr_defs.append(instr_file_name);


def find_function_names(): 
    with os.popen('grep -nr "function " '+sail_model_dir+' | grep -v "execute" | grep -v "clause" | grep -v "scattered"') as res: 
        for fn_def in res: 
            if "(" not in fn_def: 
                continue; 
            print(fn_def);
            fn_def_split = fn_def.split(":");
            fn_file_name = fn_def_split[0];
            fn_line_num = int(fn_def_split[1]);
            fn_name = fn_def_split[2].split("(")[0];
            if fn_name.find("function", 0) == -1:
                continue;
            fn_name = fn_name.split("function ")[1].split(" ")[0];
            #if fn_name not in functions_to_ignore: 
            function_names.append(fn_name);
            if fn_file_name not in files_to_scan_for_func_defs:
                files_to_scan_for_func_defs.append(fn_file_name);

def find_register_names(): 
    with os.popen('grep -nr "register " '+sail_model_dir+' | grep -v "function" | grep -v "execute" | grep -v "val" | grep -v "scattered"') as res: 
        for reg_dec in res: 
            if "//" in reg_dec or '"' in reg_dec or "*/" in reg_dec: 
                continue; 
            print(reg_dec);
            reg_dec_split = reg_dec.split(":");
            reg_file_name = reg_dec_split[0];
            reg_line_num = int(reg_dec_split[1]);
            reg_name = reg_dec_split[2];
            print(reg_name);
            if reg_dec.find("register", 0) == -1:
                continue;
            reg_name = reg_name.split("register ")[1].split(" ")[0];    
            if reg_name == '' or reg_name == "then" or reg_name == "read": 
                continue;
            if reg_name in register_names: 
                print("Found multiple decs: "+reg_name);
                exit(0);
            register_names.append(reg_name);
            if reg_file_name not in files_to_scan_for_reg_defs:
                files_to_scan_for_reg_defs.append(reg_file_name);


find_instruction_names();
find_function_names();
find_register_names();
print(instruction_names);
print(files_to_scan_for_instr_defs);
print("\n\n");
print(function_names);
print(files_to_scan_for_func_defs);
print("\n\n");
print(register_names);
print(files_to_scan_for_reg_defs);

reduced_function_names = [];

for fn_name in function_names: 
    if "decode_" not in fn_name: 
        reduced_function_names.append(fn_name);

print("Original len: "+str(len(function_names)));
print("Reduced len: "+str(len(reduced_function_names)));

print(reduced_function_names);

instr_names_300 = [];
func_names_300 = [];
reg_names_300 = []; 

for i in range(0, 300):
    instr_names_300.append(instruction_names[i]);
    func_names_300.append(reduced_function_names[i]);
    reg_names_300.append(register_names[i]);

print("\n\n 300 len lists: instr, func, reg: \n\n");
print(instr_names_300);
print("\n\n");
print(func_names_300);
print("\n\n");
print(reg_names_300);

load_instrs = [];
store_instrs = [];
for instr in instruction_names: 
    if "LD1B" in instr: 
        load_instrs.append(instr);
    elif "ST1B" in instr: 
        store_instrs.append(instr);
    
print("\n\n Loads and stores 1B: \n\n");
print(load_instrs);
print(store_instrs);