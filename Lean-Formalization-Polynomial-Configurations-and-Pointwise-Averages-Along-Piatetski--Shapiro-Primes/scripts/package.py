#!/usr/bin/env python3
"""Package sources, documents and evidence without dependency/build caches."""
from pathlib import Path
import sys
import zipfile

root = Path(__file__).resolve().parent.parent
output = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else root.parent / 'output' / 'PSPrimes_Formalization_Project.zip'
output.parent.mkdir(parents=True, exist_ok=True)
excluded_dirs = {'.git', '.lake', '__pycache__', 'web'}
excluded_suffixes = {'.aux', '.out', '.fls', '.fdb_latexmk', '.toc', '.paux', '.pyc'}
with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    archive.comment = b'Conditional Lean formalization; see README.md, docs/ASSUMPTIONS.md and evidence/VERIFICATION.md.'
    for path in sorted(root.rglob('*')):
        if not path.is_file():
            continue
        relative = path.relative_to(root)
        if any(part in excluded_dirs for part in relative.parts) or path.suffix in excluded_suffixes:
            continue
        info = zipfile.ZipInfo(str(Path('PSPrimes') / relative), (2026, 10, 30, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = (path.stat().st_mode & 0o777) << 16
        archive.writestr(info, path.read_bytes())
with zipfile.ZipFile(output) as archive:
    bad = archive.testzip()
    if bad:
        raise SystemExit('Archive integrity failed at ' + bad)
    print(f'{output}: {len(archive.infolist())} files, {output.stat().st_size} bytes; integrity passed')
