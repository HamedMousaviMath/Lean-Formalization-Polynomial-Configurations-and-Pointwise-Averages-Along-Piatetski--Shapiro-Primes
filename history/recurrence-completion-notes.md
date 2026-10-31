# Recurrence completion handoff — 30 October 2026

This is the retained implementation handoff, to be incorporated into the single chronological development log. It is not a separate formalization milestone or a substitute for the final global build/audit.

## Checked original deductions

`DensityIncrement.lean` proves the manuscript's Proposition 3.1 conditionally on the two *separate* primitive KMTT results. `KMTTUnweightedInput` supplies only ordinary-prime-to-unweighted discrepancy. `KMTTRegularityInput` supplies only the literal small-scale alternative or actual arithmetic-progression partitions with their projections and coordinate-dependent resolutions. The original step to a denser atom is proved using `Density.lean`; the numerical lcm compatibility (source (5.36)), exclusion of the small-scale alternative, transfer from the shorter scale, and positive explicit progression length are also proved. The common modulus exponent is chosen from d before ℓ,C, and the q/δ length exponents from d,ℓ before C. The positive length prefactor is retained explicitly, not silently replaced by 1. `KMTTNormalization.lean` is another agent's checked bridge to the literal prefactor-1 convention.

`RecurrenceConstruction.lean` stores actual finite sets, positive integer sizes/moduli, the exact forbidden PS-prime configuration, and the fixed smoothness/lcm invariants. Every next stage is explicitly the affine pullback of the set onto the denser progression. Its cardinality, density gain, length, smaller ambient size and unchanged prime parameter are proved. Numerical bookkeeping is applied only to *already constructed* finite prefixes. A prefix extension adds the logarithmic length inequality only after deriving it from the current stage's verified numerical range and actual finite length bound. Thus it does not assume the admissibility or existence of future stages.

The construction chooses s=ceil(K₁ α^(−C₁)), Q₀=lcm(1,…,s), and an actual full residue-class intersection with at least the original density. The residue representation r₀∈[1−Q₀,0] and the full natural floor length are retained. The generic iteration uses H=floor(log(α⁻¹)/log(1+c₂))+1, proves its logarithmic horizon bound, establishes every next stage's admissibility from the past prefix, builds the finite prefix through H, and contradicts density≤1. The density exponent κ is selected before the PS exponent c and before the provider's scale threshold.

`MainRecurrence.lean` discharges the generic step provider using actual Lemma 3.2 and Proposition 3.1 for the same compatible KMTT parameters. Its final theorem is:

```
PSPrimes.quantitative_recurrence
  (hSS : ShaoSunPhaseInput)
  (hVN : FiniteVNInput)
  (hReg : KMTTRegularityInput)
  (hJoint : KMTTCompatibleInput)
  (P : PolynomialFamily ℓ) : QuantitativeRecurrence P
```

It automatically chooses the family's actual largest degree and a common coefficient bound. The regularity data are selected before the jointly chosen KMTT discrepancy and mass witnesses. `KMTTCompatibleInput` is an explicitly external proof-level source-selection bridge: the same c₁ must work in the source comparison and the prime-mass truncation. It is not deduced from an arbitrary previously chosen comparison witness, and no mass existence for every parameter record is assumed. No original density-increment or main-theorem conclusion appears in this final theorem's external inputs.

`QuantitativeRecurrence P` has the exact manuscript quantifier order: cstar>1 and κ>0 are chosen before every 1<c<cstar; N₀ may then depend on P,c; every A⊆[N] of cardinality at least N/(log N)^κ contains the actual polynomial configuration with a PS prime and all displayed terms pairwise distinct. The final wrapper includes the division/rpow conversion from the density threshold; the ordinary-language conclusion is not a simplified auxiliary model.

## Actual verification and review

* `lake build PSPrimes.DensityIncrement` passed. The final successful log has no new-module warnings: `evidence/density-increment-build.log`.
* Eight central density-increment theorem axiom audits passed with exactly `[propext, Classical.choice, Quot.sound]`: `evidence/density-increment-audit.log`.
* `lake build PSPrimes.RecurrenceConstruction` passed: `evidence/recurrence-construction-build.log`.
* `lake build PSPrimes.MainRecurrence` passed: `evidence/main-recurrence-build.log`. This replayed existing dependency linter warnings, but the new two modules had no warnings.
* Five central construction/main theorem axiom audits passed with exactly the three standard logical axioms: `evidence/main-recurrence-audit.log`.
* All these commands used the restored pinned Lean 4.19.0 runtime and official Mathlib artifacts, with the environment-only `/proc/exe` compatibility shim recorded in the environment notes. Project modules above were freshly compiled; Mathlib artifacts were reused.
* Final construction SHA256: `aa7b6c3bebdb6efb8f86f8c2f5f961491450225fbab5f33efcb9683123dc6aea`.
* Final main-wrapper SHA256: `b7702768ace7893f70c68508476a7c353bc3cb97f748859a2f126ce2383c7e76`.
* The mathematical reviewer independently inspected the full final source, actual initialization, past-only prefix argument, same-parameter source application, and final four-input wrapper. No mismatch or residual original-result oracle was found. Review and checked hashes are in `history/correspondence-review.md` and `history/main-recurrence-reviewed-sources.sha256`.

Exploratory whole-file checks were interrupted during heavy concurrent compilation; neither was claimed successful. A trivial Mathlib probe showed the same contention. After broad builds were serialized, the generic construction and full final wrapper checked successfully without a mathematical or elaboration workaround. The split between `RecurrenceConstruction` and `MainRecurrence` makes the constructive argument and final source selection separately readable and reusable.
