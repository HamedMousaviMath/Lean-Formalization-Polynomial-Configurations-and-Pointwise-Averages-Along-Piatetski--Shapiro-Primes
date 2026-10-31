# Restart record

## Authoritative source

`manuscript/original/Draft1.tex`, unchanged, SHA-256:

```
3876857aaa7855cc791df0be3b7b60bfbe0be249df013465dd50f72d1566a701
```

Title: *Polynomial configurations and pointwise averages along
Piatetski–Shapiro primes*. No author-supplied version, date or PDF. Compiling
the preserved source produces 14 pages; its `.aux` numbering determines the
statement map. The original manuscript has not been edited.

## Implemented and checked

Both main specifications are proved conditionally:

- `PSPrimes.quantitative_recurrence` in `MainRecurrence.lean` proves
  `QuantitativeRecurrence P`.
  The actual finite-set iteration preserves the forbidden PS-prime
  configuration, constructs each affine pullback, proves admissibility from
  the already constructed prefix and forces a density contradiction. The
  exponent κ is chosen before c; no increment-provider assumption remains in
  the final theorem.
- `PSPrimes.pointwiseErgodicTheorem_of_external_inputs` proves
  `PointwiseErgodicTheorem P` for the actual two prime averages and their
  common almost-everywhere limit. The discrepancy rate, full-sequence passage,
  higher-prime-power removal, selected-prime enumeration, discrete Abel
  unweighting and essential-L∞ normalization are proved.

All seven original numbered statements have conditional checked proofs. The
two quoted analytic statements are explicit external inputs. There is no
remaining open original-proof obligation in the final statement map. This
does not mean the external results or every source translation are formalized.

## Latest successful verification

Pinned Lean: `leanprover/lean4:v4.19.0`.
Pinned Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- After workspace recovery, `lake build PSPrimes.MainPointwise` passed;
  `evidence/recovery-main-pointwise-build.log` records fresh compilation of
  the recovered pointwise modules. Its five central theorem audits passed
  with only the three standard logical axioms:
  `evidence/recovery-pointwise-axioms.log`.
- `lake build PSPrimes.RecurrenceConstruction` and
  `lake build PSPrimes.MainRecurrence` passed. Their logs are
  `evidence/recurrence-construction-build.log` and
  `evidence/main-recurrence-build.log`; five central construction and main
  theorem audits passed in `evidence/main-recurrence-audit.log`.
- `lake build PSPrimes.LogScales` passed, deriving the uniform logarithmic
  recursion from the actual finite increment length bound.

Final clean project validation passed on 30 October 2026:
`bash scripts/check.sh` exited 0. It removed only `.lake/build`, freshly
compiled all 45 project modules and the entry point in dependency order,
audited 455 named declarations, passed the production forbidden-token scan,
and verified the unchanged manuscript hash. Only `Classical.choice`,
`Quot.sound` and `propext` appeared in the audit. Exact commands, source
hashes and outcomes are in `evidence/VERIFICATION.md`,
`evidence/project-build-manifest.json`, `evidence/clean-build.log`,
`evidence/AxiomAudit.lean` and `evidence/axiom-audit.log`.

Mathlib artifacts were reused from the official cache. Fresh project-source
compilation is distinguished from reused dependencies. Earlier failed or
interrupted setup/build attempts remain in the historical evidence and do not
count as successful verification.

## External inputs and limits

No external predicate is instantiated and no new mathematical axiom is added.
Theorem 1.1 uses `ShaoSunPhaseInput`, `FiniteVNInput`, `KMTTRegularityInput`
and `KMTTCompatibleInput`. Theorem 1.2 uses `ShaoSunPhaseInput`,
`OrbitVNInput`, `PrimeNumberTheoremInput` and `OrdinaryPrimePointwiseInput`.

Read `docs/ASSUMPTIONS.md` before modifying these interfaces. The catalogue
retains the unformalized source specializations, normalization and uniformity
bridges, including KM-J's compatible proof-level constant selection. Axiom
audits do not verify those hypotheses. Independent mathematical correspondence
reviews and reviewed-source hashes are retained in `history/`.

## Recovery and next task

The transient workspace reset after the first saved archive. Missing modules
were recovered from the original authored history; recorded pre-reset source
hashes were matched where available. The three final pointwise modules matched
all their frozen hashes byte for byte and were rebuilt and audited in the
restored environment. Earlier logs remain historical; the recovery runs are
separately named. No missing proof was replaced by an assumption.

Next mathematical task: formalize or replace the external source-to-interface
bridges, starting with the finite/supremum and orbit translations or the KM-J
joint constant selection. The primary-source inspection and independent
correspondence reviews are already recorded; they do not replace Lean proofs
of those bridges. Keep both blueprints, the map and catalogue consistent with
any extension. No original numbered deduction remains open under the current
explicit premises.
