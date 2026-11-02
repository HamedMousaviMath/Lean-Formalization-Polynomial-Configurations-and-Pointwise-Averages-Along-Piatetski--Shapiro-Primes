# Restart record — 2 November 2026

The current source is the unedited `manuscript/revised-2026-11-02/Draft.tex`,
SHA256 `1b471706e66ddad262f9e7b3d3954336710112b9f962a07831b7b681df1c9fdd`.
Its generated PDF has 15 pages; no author PDF was attached. The original
14-page prime manuscript and related sequences source remain unchanged.
Base repository commit: `d523ab623a07a1969cae0f6386d08a7e28f09c28`.

## Implemented and checked

All seven earlier numbered deductions and revised Corollary 4.2 have checked
conditional proofs. The new `lacunary_variation_of_external_inputs` proves the
actual weighted infinite variation bound, r>2, uniformly over positive
lacunary cutoffs and probability systems, with the exact product of essential
L∞ norms. The four new modules are Variation, Lacunary, VariationHomogeneity
and LongVariation. The old 48 production modules are byte-for-byte unchanged.
The required part of the author's related sequences paper remains proved
internally from finite TV; no new own-paper result is assumed.

## Latest successful verification

The final `bash scripts/check.sh`, in the recorded pinned sandbox environment,
exited 0 on 2 November 2026. It freshly compiled all 52 production modules and
the entry point (53 commands, 340.932 seconds), audited 508 named declarations,
passed the placeholder scan, and verified all three manuscript manifests.
Only `propext`, `Classical.choice` and `Quot.sound` appeared. All 46 blueprint
names and printed public interfaces checked with exit 0. Compact/full LaTeX
PDFs compile to 10/20 pages; native metadata and visual QA passed.

Lean 4.19.0, Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The 6641 dependency artifacts were reused from the official cache, separately
from fresh project compilation. Actual commands, logs and source hashes are
in `evidence/VERIFICATION.md`; sandbox restoration is `revision-environment.txt`.

## External assumptions and remaining obligations

Eight explicit interfaces remain uninstantiated. The new MW-V input quotes
MWW Theorem 1.1(iv), equation (1.5), including separately catalogued MW-V-B.
The new corollary uses SS, TV and MW-V only. The two original main theorems
retain their old premises and jointly use six interfaces. All deep theorems
and remaining source bridges are in `docs/ASSUMPTIONS.md`; the axiom audit
establishes neither their truth nor manuscript correspondence. The endpoint
remark is conjectural, not a claimed finite-Lp theorem. No original deduction
remains open under its explicit premises. Independent human review is still
outstanding.

## History and next concrete task

The exact two manuscript edits (restore the sentence introducing η after the
shortened prime-power estimate; seven→eight interface count) are in
`docs/REVISION_2026_11_02.md`. The supplied source is unmodified.
Earlier blueprints, documentation and evidence are retained in
`history/pre-revision-2026-11-02/`; review and unedited intermediate failure
output are in `history/revision-2026-11-02/`. The chronological log remains
`docs/DEVELOPMENT_LOG.md`.

The extension is ready for the author to add to GitHub using
`INSTALL_REVISION.md`. No remote push was performed. A further mathematical
extension could discharge TV-B or the finite-Lq MWW source bridge; those are
optional future work, not silently assumed completed here.
