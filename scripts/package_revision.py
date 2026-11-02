#!/usr/bin/env python3
"""Create an additive ZIP overlay against the published pre-revision commit.

Run before committing the revision. The complete-project archive can always
be recreated with scripts/package.py after committing or extracting it.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import zipfile

root = Path(__file__).resolve().parent.parent
base = "d523ab623a07a1969cae0f6386d08a7e28f09c28"
output = (Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else
          root.parent / "output" / "PSPrimes_Revision_Extension_2026-11-02.zip")
output.parent.mkdir(parents=True, exist_ok=True)

def git_names(*args):
    return subprocess.check_output(["git", *args, "-z"], cwd=root).decode().split("\0")

names = set(git_names("diff", "--name-only", base))
names.update(git_names("ls-files", "--others", "--exclude-standard"))
names.discard("")
paths = sorted(p for p in names if (root / p).is_file())
manifest_name = "evidence/revision-overlay-files.json"
paths = [p for p in paths if p != manifest_name]
manifest = {"base_commit": base, "files": [
    {"path": p, "sha256": hashlib.sha256((root / p).read_bytes()).hexdigest()}
    for p in paths]}
(root / manifest_name).write_text(json.dumps(manifest, indent=2) + "\n")
paths.append(manifest_name)

with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    archive.comment = b"Additive revision overlay; read INSTALL_REVISION.md."
    for name in sorted(paths):
        path = root / name
        info = zipfile.ZipInfo(name, (2026, 11, 2, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = (path.stat().st_mode & 0o777) << 16
        archive.writestr(info, path.read_bytes())
with zipfile.ZipFile(output) as archive:
    bad = archive.testzip()
    if bad:
        raise SystemExit("ZIP integrity failure: " + bad)
    print(f"{output}: {len(archive.infolist())} files, {output.stat().st_size} bytes; integrity passed")
