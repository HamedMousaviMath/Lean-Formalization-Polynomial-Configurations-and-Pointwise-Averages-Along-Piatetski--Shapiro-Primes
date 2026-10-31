# Restart record

## Authoritative sources

The prime manuscript is the unchanged `manuscript/original/Draft1.tex`,
*Polynomial configurations and pointwise averages along Piatetski–Shapiro
primes*, by Hamed Mousavi. No version/date or author PDF was supplied;
compiling the source produces 14 pages. SHA-256:
`3876857aaa7855cc791df0be3b7b60bfbe0be249df013465dd50f72d1566a701`.

The subsequently supplied related sequences manuscript is preserved unchanged
as `manuscript/related-original/PSSequences.tex`. Its generated PDF has 11
pages; Proposition 1.4 (`p:orbit`), equation (10), on page 3 is the needed part.
SHA-256: `a172126d8d75e2032dd9da685cc848f8f76967b2f69c84066d87c0815a5d6a6e`.
Its unrelated arguments and main results are outside the present extension.

## Implemented and checked

All seven original prime-manuscript numbered deductions have checked
conditional proofs; Theorems 1.3 and 2.1 remain quoted external inputs.

- `quantitative_recurrence` proves the actual `QuantitativeRecurrence P`,
  including finite-set construction, affine pullbacks, smoothness,
  past-prefix admissibility and density contradiction. Its premises are
  `ShaoSunPhaseInput`, `FiniteVNInput`, `KMTTRegularityInput` and
  `KMTTCompatibleInput`. The exponent κ is chosen before c.
- `pointwiseErgodicTheorem_of_external_inputs` proves the actual
  `PointwiseErgodicTheorem P`: count-normalized prime and PS-prime averages
  with one common a.e. limit and essential L∞ hypotheses. Its premises are
  `ShaoSunPhaseInput`, `FiniteVNInput`, `PrimeNumberTheoremInput` and
  `OrdinaryPrimePointwiseInput`.
- `orbitVNInput_of_finiteVNInput : FiniteVNInput → OrbitVNInput` proves the
  exact real-weight orbit estimate needed from the related paper. It retains
  the same degree-only exponent, checks the shift P(n−1), exact spatial
  cutoffs and normalization, explicit dual multiplier, action invariance,
  integrability and one common conull set for every integer iterate.
  `OrbitVNInput` and former OR-B are no longer independent assumptions.

Seven independent external predicates remain, six used jointly by the two
mains because KM-Compatible supplies the standalone unweighted input.
`docs/ASSUMPTIONS.md` gives every actual interface and unformalized source
bridge. No new mathematical axiom or original-conclusion premise is added.

## Latest successful verification

Lean `leanprover/lean4:v4.19.0`; Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

After the orbit extension and proof-source freeze, the actual command
`source ../tooling/env.sh && flock /tmp/psprimes-orbit-lean.lock bash scripts/check.sh`
exited 0 on 30 October 2026. It removed only the project build directory,
freshly compiled all 48 modules and the entry point, audited 481 named
production declarations, passed the forbidden-token scan and checked the
original manuscript hash. Only `Classical.choice`, `Quot.sound` and `propext`
appeared. The related manuscript hash and all final source hashes also passed.

The printed public interfaces and all 36 blueprint-exported Lean names checked
with exit 0. Both revised PDFs compiled: compact 9 pages, full 18 pages;
native dependency metadata and all-page visual checks passed. See
`evidence/VERIFICATION.md` for commands, outcomes and artifact locations.
Mathlib artifacts were reused from the official cache, not freshly rebuilt.

## History and next task

The initial workspace reset and source recovery are recorded chronologically
in `docs/DEVELOPMENT_LOG.md`; pre-reset hashes matched at recovery where
available. The orbit extension subsequently changed the pointwise proof chain.
Older reviews, verification results, PDFs and raw development notes remain
historical under `history/`, including `before-orbit-verification/` and
`blueprint-before-orbit/`. The current independent integration review and six
verified hashes are `history/orbit-transference-review.md` and
`history/orbit-transference-reviewed-sources.sha256`.

No original prime-manuscript deduction remains open under its explicit
premises, and no independent result of the related paper remains assumed.
A possible next extension is to formalize TV-B or the MWW source specialization
using the proved shift identities. The permitted deep external inputs and the
remaining catalogue bridges are still unproved; an axiom audit does not
establish their truth. Keep the map and both blueprints synchronized with any
further change.
