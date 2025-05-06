# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# ---------------------------- Author: Neelu S. Kalani (neelu.kalani@ibm.com/neelukalani7@gmail.com) --------------------------------------------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #
# -------------- This file defines a list of keywords or operators which are specific to Sail, and some which are specific to RISC-V ------------------- #
# -------------- These are used by the sail_lexer module to define pattern constructors (identify function calls, or parse expressions) ---------------- #
# -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- # -------------- #

from plex import *;

# --------------------------------------------------- Sail specific: keywords and operators ------------------------------------------------------------- #

# (Sources: Sail manual, and VSCode Sail Syntax Highlighter/Parser Code (https://github.com/rems-project/sail/blob/sail2/editors/vscode/sail/syntaxes/sail.tmLanguage.json#L47))
keywords_of_interest = Str("type", "val", "function", "scattered", "clause", "default", "register", "bitfield", "mapping") + Str(" ");
keywords_to_ignore = Str("let", "effect", "rec", "and", "option", "bool", "true", "false", "bit", "bitzero", "bitone", "unit", "nat", "int", "int8", "int16", "int32", "int64", "typedef", "const", "struct", "string", "range", "atom", "vector", "list", "enumerate", "bits", "alias", "extern", "forall", "foreach", "sizeof", "rreg", "wreg", "rmem", "wmem", "wmv", "barr", "depend", "undef", "unspec", "nondet", "escape", "lset", "lret", "pure", "switch", "case", "foreach", "from", "to", "by", "in", "of", "downto", "return", "exit", "assert", "undefined", "if", "then", "else", "with", "sizeof", "hex", "bin", "union", "registerbits", "member", "inc", "dec", "end");

# Source: Sail manual, chapter 7. 
# Bitwise not, or, xor, and, left-shift, right-shift, rotate. Arithmetic add, add signed, subtract, subtract signed, multiply, multiply signed, power, 
# equal to, not equal to, other comparisonssss.... 
operators = Str('~', '|', '^', '&', '<<', '>>', '<<<', '+', '+_s', '-', '-_s', '*', '*_s', '**', '==', '!=', '<', '<_u', '<_s', '>', '>_u', '>_s', '<=', '<=_s', '>=', '>=_s');
comparison_operators = Str('==', '!=', '<', '<_u', '<_s', '>', '>_u', '>_s', '<=', '<=_s', '>=', '>=_s');
# The operators fitting with 'name' are ignored at the moment. e.g. 'div', 'mod'. I don't see them being used in such a way at least in the risc-v implementation. 

# --------------------------------------------------- Sail specific: ignore printing ------------------------------------------------------------- #

print_reg_pattern = Str("print", "print_platform", "print_reg", "print_bits", "print_mem", "print_instr") + Str("("," (") + Rep(AnyBut(";")) + Str(";");

