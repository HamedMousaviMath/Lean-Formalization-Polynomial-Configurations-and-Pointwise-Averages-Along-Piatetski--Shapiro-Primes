#!/usr/bin/env python3
"""Fresh project build in dependency order, reusing pinned Mathlib artifacts.

Serial target invocation avoids duplicate import/page-fault pressure in
constrained runtimes. Each actual lake command and result is logged.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
paths = {f'PSPrimes.{p.stem}': p for p in (root / 'PSPrimes').glob('*.lean')}
paths['PSPrimes'] = root / 'PSPrimes.lean'
deps = {}
for name, path in paths.items():
    deps[name] = [n for n in re.findall(r'^import\s+(\S+)', path.read_text(), re.M) if n in paths]
order, active, done = [], set(), set()
def visit(name):
    if name in done:
        return
    if name in active:
        raise SystemExit('Local import cycle at ' + name)
    active.add(name)
    for dep in deps[name]:
        visit(dep)
    active.remove(name)
    done.add(name)
    order.append(name)
for name in sorted(paths):
    visit(name)
manifest = []
for name in order:
    path = paths[name]
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    command = ['lake', 'build', name]
    print('$ ' + ' '.join(command), flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=root)
    manifest.append({'module': name, 'source': str(path.relative_to(root)),
                     'sha256': digest, 'command': command,
                     'exit_code': result.returncode, 'seconds': round(time.monotonic() - start, 3)})
    (root / 'evidence' / 'project-build-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    if result.returncode:
        raise SystemExit(result.returncode)
print(f'Serialized project build passed: {len(order)} modules including entry point.', flush=True)
