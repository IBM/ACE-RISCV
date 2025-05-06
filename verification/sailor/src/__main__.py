# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #

import sys;
import scanner.scanner;
import analyzer.analyzer;
import verifier.verifier; 

if len(sys.argv) != 6: 
    print("Please provide archictecture, sail index directory, sail model directory and result directory, and isla traces file as command line args.");
    print("E.g. python3 main.py riscv64 <path-to-sail-index-dir> <path-to-sail-model-dir> <path-to-results-dir> <path-to-isla-traces-file>");
    print("The results directory is just where you want all the results of Sailor to be output.");
    print("Architectures supported by Sailor: 'riscv64', 'riscv64-hext' (with hypervisor extension)");
    exit(0);

# TODO: Arch argument sanity check

scanner.scanner.main(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]);
analyzer.analyzer.main(sys.argv[1], sys.argv[4]);
#verifier.verifier.main(sys.argv[1], sys.argv[4], sys.argv[5]);

#analyzer.main("riscv64");

#scanner.main("riscv64-hext", "../../riscv-hext-sail/model/");

#analyzer.main("riscv64");