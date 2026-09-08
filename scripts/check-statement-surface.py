#!/usr/bin/env python3
"""Check the two deliberately small, Mathlib-only Palomar statement files."""
from pathlib import Path
import json
import re
import subprocess
import sys

repository = Path(__file__).resolve().parent.parent
project = repository / sys.argv[1]
challenge = project / 'Challenge.lean'
source = challenge.read_text()
config = json.loads((project / 'comparator.json').read_text())
assert len(source.encode()) <= 102400, 'Challenge exceeds Palomar byte limit'
assert len(source.splitlines()) <= 300, 'Keep the Challenge below the warning threshold'
imports = re.findall(r'^import\s+(\S+)', source, re.M)
assert imports and all(name.startswith('Mathlib.') for name in imports), imports
names = re.findall(r'^theorem\s+(\w+)', source, re.M)
assert len(names) == 1, names
assert config['theorem_names'] == ['ProofOfSpaceStatement.' + names[0]], config
assert config['definition_names'] == []
assert config['enable_nanoda'] is True
assert len(re.findall(r'\bsorry\b', source)) == 1
# Resolve the imports with Lean as well, to reject local modules shadowing Mathlib.
result = subprocess.run(['lake', 'env', 'lean', '--src-deps', 'Challenge.lean'],
                        cwd=project, capture_output=True, text=True, check=True)
mathlib = (project / '.lake/packages/mathlib/Mathlib').resolve()
prefix = subprocess.run(['lake', 'env', 'lean', '--print-prefix'], cwd=project,
                        capture_output=True, text=True, check=True).stdout.strip()
core = (Path(prefix) / 'src/lean').resolve()
for line in result.stdout.splitlines():
    dep = Path(line.strip())
    if not dep.is_absolute(): dep = project / dep
    dep = dep.resolve()
    if dep == challenge.resolve(): continue
    if not (dep.is_relative_to(mathlib) or dep.is_relative_to(core)):
        raise SystemExit('Challenge import outside Mathlib and Lean: ' + str(dep))
print(f'{sys.argv[1]}: {len(source.splitlines())} lines; one theorem; Mathlib-only statement imports')
