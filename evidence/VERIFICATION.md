# Verification after the manuscript revision — 2 November 2026

The production project now has **52 modules and its entry point**, including
four added modules: Variation, Lacunary, VariationHomogeneity and LongVariation.
The old 48 modules are byte-for-byte unchanged from repository base commit
`d523ab623a07a1969cae0f6386d08a7e28f09c28`; only the entry imports were extended.
See `revision-correspondence-check.json`.

## Actual clean build and audit: passed

The actual command, from the project root, was:

```sh
env PATH=/workspace/scratch/c84b5d813ddd/lean-environment/lean-4.19.0-linux/bin:$PATH LD_PRELOAD=/workspace/scratch/c84b5d813ddd/lean-environment/proc_exe_compat.so bash scripts/check.sh > evidence/revision-extension-check.log 2>&1
```

It exited **0**. The script removed only this project's `.lake/build` and
freshly compiled all 53 targets in dependency order. Every target exited 0;
total target invocation time was **340.932 seconds**. The manifest records each
command, source SHA256, duration and exit code in `project-build-manifest.json`.
The complete output is `clean-build.log` and `revision-extension-check.log`.
Nonfatal tactic-style/unused-variable suggestions remain in older modules;
the four new modules have no linter warnings.

`python3 scripts/audit.py`, invoked by that same check, generated
`AxiomAudit.lean` and ran `lake env lean evidence/AxiomAudit.lean` successfully.
It audited **508 named declarations**, reporting only `propext`,
`Classical.choice` and `Quot.sound`. No additional mathematical axiom appeared.
The production forbidden-token scan passed for sorry, admit, axiom, unsafe
and native_decide outside comments. The script also checked the original,
related and revised manuscript SHA256 manifests; all passed.

The axiom audit does not prove external predicates true or establish faithful
manuscript correspondence. Those distinct obligations were reviewed separately.

## Pinned environment and provenance

Lean 4.19.0 (official commit 6caaee842e94); Lake 5.0.0-6caaee8; Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine dependency heads match
`lake-manifest.json`. The **6641 official dependency artifacts were reused**;
Mathlib was not freshly rebuilt. Project sources were freshly compiled.
`revision-environment.txt` records the actual restoration, official binary hash,
dependency revisions and successful cache download. This sandbox uses the
existing executable-path compatibility shim in `scripts/environment/`; the
Lean executable and kernel are unmodified. Ordinary installations need no shim:

```sh
lake exe cache get
bash scripts/check.sh
```

Before the extension, a separate fresh build of the original 48 modules and
entry point also passed (49 commands, 302.852 seconds), recorded in
`revision-base-build.log` and `revision-base-build-manifest.json`. The final
53-target clean build supersedes intermediate module builds. An initially
failed concurrent development build is retained under
`history/revision-2026-11-02/initial-concurrent-build.log`; it is not counted
as a successful verification.

## Public interfaces and blueprints: passed

Both commands actually ran and exited 0:

```sh
lake env lean evidence/PublicInterfaces.lean > evidence/public-interfaces.log 2>&1
lake env lean evidence/BlueprintDeclarations.lean > evidence/blueprint-declarations.log 2>&1
```

The first prints the eight external interfaces, derived orbit specification,
original main specifications and full new corollary. The second checks all
**46** names exported by native leanblueprint, including the new variation
chain, summation and normalization declarations.

Both updated LaTeX documents compiled: compact **10 pages**, full **20 pages**.
Native leanblueprint graph generation also exited 0; all uses/proves targets
resolve. The 30 pages were rendered and visually reviewed, with changed pages
checked individually. No overfull boxes, undefined references or TeX errors.
Optional vector-imager warnings are documented; the graph and MathJax output
were produced. Actual commands, logs, metadata and QA are in
`blueprint/VERIFICATION.txt` and the revision-prefixed files alongside it.

The revised manuscript was compiled twice by pdflatex with halt-on-error,
producing 15 pages. Its 49 unique labels cover 10 labelled statements and 39 equations;
the extra unlabelled Remark 1.3 is explicitly conjectural. Teräväinen is now
Theorem 1.4, and the new corollary is 4.2. No separately supplied PDF was available.

## Verified scope and remaining external boundary

All seven earlier deductions and new Corollary 4.2 have checked conditional
proofs. The two quoted statements remain external. The endpoint remark is
not asserted as a theorem. New `lacunary_variation_of_external_inputs` uses
SS, TV and MW-V only, with true infinite variation and exact essential-norm
product, including zero factors. Its constants have the manuscript's uniformity.
The two earlier main theorems retain their previous premises. No independent
result from the author's other paper is added.

MW-V quotes MWW Theorem 1.1(iv), equation (1.5), via the separately documented
unformalized bridge MW-V-B. All eight interfaces and other remaining bridges
are precisely catalogued in `docs/ASSUMPTIONS.md`. Mathematical review was by
AI collaborators and the primary agent, not independent human experts.
The two expository manuscript replacements are in `docs/REVISION_2026_11_02.md`.
The supplied revised source is unedited, hash
`1b471706e66ddad262f9e7b3d3954336710112b9f962a07831b7b681df1c9fdd`.

Earlier verification, blueprints, documentation and raw notes are retained
under `history/`. They refer to their historical versions. Only the current
revision evidence should be used for counts and current status.
