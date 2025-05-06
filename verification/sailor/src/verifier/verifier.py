# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #

from riscv import ctrl_reg_names;
import csv;
import re; 

sailor_instruction_CSR_footprint = {};
isla_csr_footprint_of_instruction = {}; 
registers_not_in_csr_list = [];
isla_entry_doesnt_exist = [];

instructions_not_verified = 0;
instructions_not_verified_list = [];
diff_instructions_not_verified = {};
instructions_verified = 0;

CSR_footprint_of_instruction_without_bitfields = {};    # To compare with Isla

scanner_results_dir = "/scanner-results/";
arch_scanner_results_dir = "";

def list_subset(larger_list, smaller_list):
  return all(item in larger_list for item in smaller_list)

def verify_sailor_results_against_isla_results(): 
    global sailor_instruction_CSR_footprint;
    global isla_csr_footprint_of_instruction;
    global arch_scanner_results_dir;
    global CSR_footprint_of_instruction_without_bitfields;
    global isla_entry_doesnt_exist;
    global instructions_not_verified;
    global instructions_not_verified_list;
    global instructions_verified;

    with open(arch_scanner_results_dir+'csr-footprint-per-instruction.csv', mode ='r') as infile:
        reader = csv.reader(infile)
        for row in reader:
            key = row[0];
            values = row[1:len(row)-1];
            while '' in values:
                values.remove('');
            while ' ' in values: 
                values.remove(' ');
            sailor_instruction_CSR_footprint[key] = values;

    # for instr in keys.... compare for each. Isla must be a subset of whatever Sailor is capturing! 
    
    print("\n\nSorted Sailor Keys: ");
    sorted_sailor_keys = sorted(sailor_instruction_CSR_footprint.keys());
    for key in sorted_sailor_keys:
     print(f"{key}")

    # TODO: This check is not specific to bitfields.    --- Can we generate bitfields deps from Isla? 
    # Processing instruction footprint to remove all bitfield info... 

    # Prepping Sailor results for comparison 
    for instr in sailor_instruction_CSR_footprint.keys(): 
        CSR_footprint_of_instruction_without_bitfields[instr] = [];
        for entry in sailor_instruction_CSR_footprint[instr]: 
            entry_without_bitfield = re.sub(f"\[.*?\]", "", entry);
            if entry_without_bitfield not in CSR_footprint_of_instruction_without_bitfields[instr]: 
                CSR_footprint_of_instruction_without_bitfields[instr].append(entry_without_bitfield);
    
        print("\nWith bitfields: \n");
        print(sailor_instruction_CSR_footprint[instr])
        print("\nWithout bitfields: \n");
        print(CSR_footprint_of_instruction_without_bitfields[instr]);

    sailor_results_prepped_for_cmp = {};
    for key, value in CSR_footprint_of_instruction_without_bitfields.items(): 
        if "C_" in key: 
            new_key = key.replace("C_", "");
            sailor_results_prepped_for_cmp[new_key] = value; 
        elif "FENCE_" in key: 
            new_key = key.replace("FENCE_", "FENCE.");
            sailor_results_prepped_for_cmp[new_key] = value;
        else: 
            sailor_results_prepped_for_cmp[key] = value;


    for instr in sailor_results_prepped_for_cmp.keys(): 
        for csr in ctrl_reg_names: 
            if csr+" Read" in sailor_results_prepped_for_cmp[instr] and csr+" Write" in sailor_results_prepped_for_cmp[instr]:
                sailor_results_prepped_for_cmp[instr].remove(csr+" Read");
                sailor_results_prepped_for_cmp[instr].remove(csr+" Write");
                sailor_results_prepped_for_cmp[instr].append(csr+" R+W");

    # Prepping Isla results for comparison 
    isla_results_prepped_for_cmp = {}; 
    for key, value in isla_csr_footprint_of_instruction.items(): 
        if "AMO" in key: 
            new_key = "AMO";
            if new_key not in isla_results_prepped_for_cmp:
                isla_results_prepped_for_cmp[new_key] = [];
            for elem in value: 
                if elem not in isla_results_prepped_for_cmp[new_key]:
                    isla_results_prepped_for_cmp[new_key].append(elem);
        else: 
            isla_results_prepped_for_cmp[key] = value;

    for instr in isla_results_prepped_for_cmp.keys(): 
        for csr in ctrl_reg_names: 
            if csr+" Read" in isla_results_prepped_for_cmp[instr] and csr+" Write" in isla_results_prepped_for_cmp[instr]:
                isla_results_prepped_for_cmp[instr].remove(csr+" Read");
                isla_results_prepped_for_cmp[instr].remove(csr+" Write");
                isla_results_prepped_for_cmp[instr].append(csr+" R+W");
        #print("\nProcessed footprint of instruction: "+instr+"\n");
        #print(isla_csr_footprint_of_instruction[instr]);
    
    # Comparing the results 
    for instr in sailor_results_prepped_for_cmp.keys(): 
        if instr in isla_results_prepped_for_cmp.keys(): 
            if not list_subset(sailor_results_prepped_for_cmp[instr], isla_results_prepped_for_cmp[instr]): 
                instructions_not_verified = instructions_not_verified + 1; 
                instructions_not_verified_list.append(instr);
                
                diff_list = [];

                for item in isla_results_prepped_for_cmp[instr]:
                    if item not in sailor_results_prepped_for_cmp[instr]:
                        diff_list.append(item);
                
                print("Diff list for "+instr);
                print(diff_list);
                
            else: 
                instructions_verified = instructions_verified + 1;
        else: 
            isla_entry_doesnt_exist.append(instr);

    if instructions_not_verified == 0: 
        print("Verification successful.");
    else: 
        print("Instructions not verified len: "+str(instructions_not_verified)+" list: ");
        print(instructions_not_verified_list);
        print(diff_instructions_not_verified);

    print("Instructions verified: "+ str(instructions_verified));

def main(argv_arch, argv_results_dir, argv_trace_file):
    global arch_scanner_results_dir;
    global sailor_instruction_CSR_footprint;
    global isla_csr_footprint_of_instruction;
    global registers_not_in_csr_list;

    arch_scanner_results_dir = argv_results_dir + scanner_results_dir + argv_arch + "/";     

    isla_traces_file = open(argv_trace_file, 'r');
    isla_traces_file_lines = isla_traces_file.readlines();

    current_instruction = "";
    
    for line in isla_traces_file_lines: 
        if "INSTRUCTION CONSTRUCTED" in line: 
            if current_instruction != "":
                print("\nCaptured Isla footprint of instruction: "+current_instruction+"\n");
                print(isla_csr_footprint_of_instruction[current_instruction]);
            current_instruction = line.split(":")[1].replace(" ", "");
            print("Found new instruction: "+current_instruction);
            isla_csr_footprint_of_instruction[current_instruction] = [];
        elif "(read-reg" in line: 
            csr = line.split("|")[1];
            if csr in ctrl_reg_names and csr+" Read" not in isla_csr_footprint_of_instruction[current_instruction]: 
                isla_csr_footprint_of_instruction[current_instruction].append(csr+" Read");
            else: 
                registers_not_in_csr_list.append(csr);
        elif "(write-reg" in line: 
            csr = line.split("|")[1];
            if csr in ctrl_reg_names and csr+" Write" not in isla_csr_footprint_of_instruction[current_instruction]: 
                isla_csr_footprint_of_instruction[current_instruction].append(csr+" Write");
            else: 
                registers_not_in_csr_list.append(csr);

    # TODO: Dump CSR footprint generated from Isla to a CSV 

    print("Isla footprints: \n\n");
    print(isla_csr_footprint_of_instruction);
    print("\n\n");

    print("Len of isla footprints: "+str(len(isla_csr_footprint_of_instruction)));

    print("\n\nSorted Isla Keys: "); 
    sorted_isla_keys = sorted(isla_csr_footprint_of_instruction.keys());
    for key in sorted_isla_keys:
     print(f"{key}")


    verify_sailor_results_against_isla_results();
            
        