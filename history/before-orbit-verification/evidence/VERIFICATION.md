# Final verification — 30 October 2026

The final production sources are the 45 modules in `PSPrimes/` and the
`PSPrimes.lean` entry point. Historical drafts under `work/` are not production
modules. All seven original numbered deductions, including both main theorems,
have checked conditional proofs; the external inputs remain uninstantiated.

## Pinned environment

- Lean `leanprover/lean4:v4.19.0`, official release commit `6caaee842e94`.
- Lake `5.0.0-6caaee8`.
- Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Exact transitive dependency revisions: `lake-manifest.json`.

Mathlib's 6,641 official cached dependency artifacts were downloaded and reused.
This is a fresh build of the project sources, not a fresh build of Mathlib.
`ENVIRONMENT.txt`, `mathlib-cache.log` and `build-environment.txt` retain the
actual setup and version evidence. The sandbox required the executable-path
compatibility shim in `scripts/environment/`; the Lean binary and kernel
were not modified. Ordinary installations do not need that shim.

## Clean build and axiom audit: passed

Actual command, from the project root in this environment:

```sh
source ../tooling/env.sh && bash scripts/check.sh
```

The setup file supplies the official Lean path and environment shim. On an
ordinary installation, install the pinned toolchain, run `lake exe cache get`,
then run `bash scripts/check.sh` directly.

The final command exited **0**. Its script:

1. Recorded the actual toolchain and Mathlib revision.
2. Removed only `.lake/build` and compiled all 45 project modules and the
   entry point in dependency order. All 46 `lake build <module>` invocations
   exited 0; their total invocation time was 324.137 seconds.
3. Generated and ran `lake env lean evidence/AxiomAudit.lean`, auditing
   **455 named project declarations**. Lean exited 0. The only axioms observed
   were `Classical.choice`, `Quot.sound` and `propext`.
4. Passed the production source scan for `sorry`, `admit`, `axiom`, `unsafe`
   and `native_decide` outside comments.
5. Passed `sha256sum -c manuscript/SHA256SUMS` and recorded all production
   source hashes. The recorded source hashes were separately rechecked.

Evidence: `clean-build.log`, `project-build-manifest.json` (actual command,
source hash, exit status and duration for every target), `AxiomAudit.lean`,
`axiom-audit.log`, `audit-summary.txt`, `source-sha256.txt`, and
`manuscript-integrity.log`.

The build emitted only nonfatal tactic-style and unused-variable linter
warnings, retained in the log. An earlier concurrent clean-build attempt was
cancelled and is explicitly recorded in `checkpoint-clean-build-cancelled.txt`;
it is not counted as a successful check.

## Mathematical correspondence

Independent reviews inspected both main statements, the finite comparison,
literal Proposition 3.1 normalization, and the source-to-interface boundaries.
The final statement map covers all 48 manuscript labels: nine numbered
statements and 39 numbered equations, plus substantial unnumbered arguments.
The current reviewed-source hashes in
`history/final-correspondence-reviewed-sources.sha256` all passed.

Historical hash records remain unchanged. The older main-recurrence review's
`Definitions.lean` hash predates a status-comment update and therefore differs;
the final review records and verifies the current source. Proof statements
were unchanged by that comment edit.

The manuscript's original SHA-256 is
`3876857aaa7855cc791df0be3b7b60bfbe0be249df013465dd50f72d1566a701`.
Only LaTeX was supplied; compiling it produced 14 pages. No necessary
manuscript correction was demonstrated.

An axiom audit does not establish the truth of explicit mathematical premises
or prove manuscript correspondence. Read `docs/ASSUMPTIONS.md` for the eight
named external predicates, the exact main-theorem premises, and every
unformalized specialization, uniformity and joint-selection bridge.

## Public interfaces and blueprints

Both additional checks ran successfully with exit 0:

```sh
lake env lean evidence/PublicInterfaces.lean > evidence/public-interfaces.log 2>&1
lake env lean evidence/BlueprintDeclarations.lean > evidence/blueprint-declarations.log 2>&1
```

The first prints all eight external predicate interfaces and both main
specifications, and checks all seven proved manuscript declarations. The
second checks all 35 names exported by native leanblueprint.

Both blueprint PDFs compiled successfully: compact **8 pages**, full
expository **17 pages**. All dependency tags resolve; PDF logs contain no
overfull boxes, undefined references or TeX errors. Native leanblueprint web
generation succeeded. All 25 pages were rendered and visually checked; the
final manual DAG was also inspected at readable resolution. Exact commands,
metadata validation, QA and final PDF/source hashes are recorded in
`blueprint/VERIFICATION.txt`, `blueprint/source-hashes.txt` and the associated
build logs. Optional native vector-imager discovery reported missing tools;
MathJax and dependency-graph output were generated successfully.

A separate final inventory check found exactly 48 active manuscript labels,
each occurring once in `docs/PAPER_MAP.md`. This check and the final PDF/source
hash checks passed. The native generated HTML can be reproduced using the
packaged source and requirements; dependency and web build caches are omitted
from the source archive.
