# Final verification after the orbit extension — 30 October 2026

The production library consists of **48 modules** in `PSPrimes/` and the
`PSPrimes.lean` entry point. Historical drafts under `work/` are excluded.
All seven original numbered prime-paper deductions have checked conditional
proofs. The required orbit estimate from the related sequences paper is now
proved from finite VN; no independent own-paper premise remains.

## Pinned environment and build provenance

Lean `leanprover/lean4:v4.19.0`, official commit `6caaee842e94`; Lake
`5.0.0-6caaee8`; Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
`lake-manifest.json` pins the transitive dependencies.

The 6,641 official Mathlib dependency artifacts were downloaded and reused.
This is a fresh build of all project sources, not a fresh dependency rebuild.
`ENVIRONMENT.txt`, `mathlib-cache.log` and `build-environment.txt` record the
actual setup and version evidence. This sandbox required the executable-path
compatibility shim in `scripts/environment/`; neither the Lean binary nor its
kernel was modified. Ordinary installations do not need the shim.

## Complete clean build and audit: passed

After freezing the production proof sources, the actual environment command
was:

```sh
source ../tooling/env.sh && flock /tmp/psprimes-orbit-lean.lock bash scripts/check.sh > evidence/orbit-extension-check.log 2>&1
```

It exited **0**. The environment file selects the official Lean release and
sandbox shim; the lock serializes compiler jobs. On an ordinary installation,
install the pinned toolchain, run `lake exe cache get`, then run
`bash scripts/check.sh`.

The check removed only `.lake/build` and invoked the serial dependency-order
builder. All **49 target commands** (48 modules plus entry point) exited 0,
with total invocation time **391.937 seconds**. The actual command, source
hash, result and duration for each target are in `project-build-manifest.json`.
`clean-build.log` records the complete build output. The only warnings were
nonfatal tactic-style and unused-variable linter suggestions.

The generated `lake env lean evidence/AxiomAudit.lean` audited **481 named
production declarations** and exited 0. Only `Classical.choice`, `Quot.sound`
and `propext` appeared. The production scan for `sorry`, `admit`, `axiom`,
`unsafe` and `native_decide` outside comments passed. Evidence:
`AxiomAudit.lean`, `axiom-audit.log`, `audit-summary.txt`.

The original prime manuscript hash passed within the check. These additional
actual checks also passed:

```sh
sha256sum -c manuscript/related-original/SHA256SUMS
sha256sum -c evidence/source-sha256.txt
sha256sum -c history/orbit-transference-reviewed-sources.sha256
sha256sum -c evidence/blueprint/source-hashes.txt
```

The first two outputs are retained in `related-manuscript-integrity.log` and
`final-source-integrity.log`. The original source hash is
`3876857aaa7855cc791df0be3b7b60bfbe0be249df013465dd50f72d1566a701`;
the related source hash is
`a172126d8d75e2032dd9da685cc848f8f76967b2f69c84066d87c0815a5d6a6e`.

## The removed assumption and correspondence review

The actual new theorem is:

```lean
orbitVNInput_of_finiteVNInput
  (hVN : FiniteVNInput) : OrbitVNInput.{u}
```

It proves the arbitrary-real-weight, essentially 1-bounded specialization of
the supplied related paper's Proposition 1.4 needed by the prime paper. The
proof checks degree-preserving translation by −1, one fixed spatial support
constant, exact finite sums and normalization, explicit complex duality,
measure preservation, integrability and a common conull set controlling all
integer iterates. It retains exactly finite VN's degree-only exponent.
`OrbitVNInput` is a derived specification; its former OR-B bridge is discharged.

All three public `ps_orbit_*` declarations and Theorem 1.2 now take finite VN
directly. The main specifications and finite VN input were not strengthened or
changed to obtain this result. Theorem 1.2's exact premises are Shao–Sun,
finite Teräväinen VN, PNT and MWW. The recurrence premises are unchanged.
Independent mathematical and integration review passed; the signed review
and six current source hashes are under `history/orbit-transference-*`.

Seven independent external predicates remain, six used jointly by the mains.
The published deep estimates and bridges SS-finiteX, TV-B, MW-B, KM-U-B,
KM-R-B and KM-J remain unformalized. Their exact interfaces and scope are in
`docs/ASSUMPTIONS.md`. Axiom audits do not prove those predicates true or
establish manuscript correspondence; these obligations are separately recorded.
The other arguments and main results of the related paper are not claimed
formalized. No necessary prime-manuscript correction was demonstrated.

## Public interfaces and documents: passed

Both additional actual Lean commands exited 0:

```sh
lake env lean evidence/PublicInterfaces.lean > evidence/public-interfaces.log 2>&1
lake env lean evidence/BlueprintDeclarations.lean > evidence/blueprint-declarations.log 2>&1
```

The first prints all seven external predicates, the derived orbit specification
and both main specifications, then checks all seven manuscript deductions and
the new transfer theorem. The second checks all **36** native-blueprint exported
names against the compiled project.

Both revised PDFs compiled: compact **9 pages**, full expository **18 pages**.
Their logs contain no overfull boxes, undefined references or TeX errors.
Native leanblueprint generation succeeded; all dependency tags resolve.
All 27 pages were rendered and visually checked. The native optional vector
imagers were unavailable; dependency-graph and MathJax output were generated.
Commands, metadata validation, QA and source/PDF hashes are in
`blueprint/VERIFICATION.txt`, `blueprint/source-hashes.txt` and associated logs.

The prime-manuscript map still covers all 48 original labels exactly once:
nine numbered statements and 39 equations, plus substantial unnumbered steps.
The new related-paper deduction has a separate correspondence entry.
The preserved related source compiled to 11 pages, confirming Proposition 1.4,
equation (10), on page 3; its build log is `related-manuscript-build.log`.

## Historical evidence

The earlier 45-module/455-declaration verification and documents are retained
under `history/before-orbit-verification/` and `history/blueprint-before-orbit/`.
Earlier source-review hashes refer to their historical versions and need not
match the subsequently revised pointwise chain or map. The current orbit
review hashes do match. An earlier cancelled concurrent clean build remains
explicitly recorded as cancelled and is not counted as successful evidence.
Dependency and generated web caches are omitted from the distributable archive;
the native web output is reproducible from packaged source and requirements.
