#!/usr/bin/env python3
import re
import sys

if len(sys.argv) < 3:
    print("usage: prune_dune_modules.py <dune-file> <module1> [module2 ...]")
    sys.exit(1)

path = sys.argv[1]
remove = set(sys.argv[2:])

with open(path) as f:
    text = f.read()

# Matches: (modules ... )
pattern = re.compile(r'\(modules\b([^)]*)\)')

def prune(match):
    modules = match.group(1).split()
    kept = [m for m in modules if m not in remove]
    return "(modules " + " ".join(kept) + ")"

new_text = pattern.sub(prune, text)

with open(path, "w") as f:
    f.write(new_text)
