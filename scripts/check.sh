#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p evidence
{
  date -u +'%Y-%m-%dT%H:%M:%SZ'
  lean --version
  lake --version
  printf 'Mathlib revision: '
  git -C .lake/packages/mathlib rev-parse HEAD
} > evidence/build-environment.txt
# Remove ONLY this project's compiled files. Dependency artifacts are reused.
rm -rf .lake/build
python3 scripts/build_serial.py 2>&1 | tee evidence/clean-build.log
python3 scripts/audit.py
sha256sum -c manuscript/SHA256SUMS | tee evidence/manuscript-integrity.log
sha256sum -c manuscript/related-original/SHA256SUMS | tee evidence/related-manuscript-integrity.log
sha256sum -c manuscript/revised-2026-11-02/SHA256SUMS | tee evidence/revised-manuscript-integrity.log
sha256sum manuscript/original/Draft1.tex > evidence/manuscript-sha256.txt
sha256sum PSPrimes.lean PSPrimes/*.lean > evidence/source-sha256.txt
