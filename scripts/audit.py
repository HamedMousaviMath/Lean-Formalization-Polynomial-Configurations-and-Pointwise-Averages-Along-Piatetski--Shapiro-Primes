#!/usr/bin/env python3
"""Generate an explicit dependency audit of all named project declarations.

The source scan is a convenience, not a replacement for kernel compilation.
The generated Lean file imports the complete project and runs #print axioms.
"""
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
sources = sorted((root / 'PSPrimes').glob('*.lean'))
pattern = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem|lemma|structure)\s+([\w.\']+)', re.M)
names = []
for path in sources:
    text = path.read_text()
    # Strip comments before the forbidden-token scan; do not mistake prose for code.
    stripped = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', stripped)
    if forbidden:
        raise SystemExit(f'{path.name}: prohibited production tokens: {forbidden}')
    scopes = []
    for line in stripped.splitlines():
        match = re.match(r'^namespace\s+([\w.]+)', line)
        if match:
            scopes.append(('namespace', match.group(1)))
            continue
        match = re.match(r'^(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$', line)
        if match:
            scopes.append(('section', match.group(1)))
            continue
        match = re.match(r'^end(?:\s+([\w.]+))?\s*$', line)
        if match:
            if not scopes:
                raise SystemExit(f'Unmatched end in {path.name}')
            kind, scope_name = scopes.pop()
            if match.group(1) and match.group(1) != scope_name:
                raise SystemExit(f'Scope mismatch in {path.name}: {line}')
            continue
        match = pattern.match(line)
        if match:
            decl = match.group(1)
            if decl.startswith('_root_.'):
                names.append(decl[len('_root_.'):])
            else:
                prefix = '.'.join(n for kind, n in scopes if kind == 'namespace')
                names.append(prefix + '.' + decl if prefix else decl)
audit = root / 'evidence' / 'AxiomAudit.lean'
audit.write_text('import PSPrimes\n\n' + '\n'.join('#print axioms ' + n for n in names) + '\n')
result = subprocess.run(['lake', 'env', 'lean', str(audit)], cwd=root,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(root / 'evidence' / 'axiom-audit.log').write_text(result.stdout)
if result.returncode:
    print(result.stdout)
    raise SystemExit(result.returncode)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
dependencies = []
for match in re.finditer(r'depends on axioms:\s*\[([^\]]*)\]', result.stdout, re.S):
    dependencies.extend(n.strip() for n in match.group(1).split(',') if n.strip())
unexpected = sorted(set(dependencies) - allowed)
if unexpected:
    raise SystemExit('Unexpected axioms: ' + ', '.join(unexpected))
message = (f'Audited {len(names)} named declarations; Lean exit 0; '
           f'axioms observed: {", ".join(sorted(set(dependencies))) or "none"}.\n'
           'No additional mathematical axioms; source forbidden-token scan passed.\n'
           'This does not establish manuscript correspondence or truth of external hypotheses.\n')
(root / 'evidence' / 'audit-summary.txt').write_text(message)
print(message, end='')
