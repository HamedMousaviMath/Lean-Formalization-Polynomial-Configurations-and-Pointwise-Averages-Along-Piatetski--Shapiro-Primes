# Reading the Lean project

Use the [compact blueprint](../blueprint/src/compact.pdf) for the mathematical
dependency graph and [PAPER_MAP.md](PAPER_MAP.md) for manuscript numbering.
This index gives a short route through the implementation. The complete
module inventory is the import list in [PSPrimes.lean](../PSPrimes.lean);
helper files are grouped below by their role, not treated as separate
mathematical milestones or blueprint nodes.

Both main conclusions are conditional implications from explicit external
predicates. To inspect their exact scope first, read
`quantitative_recurrence` in [MainRecurrence](../PSPrimes/MainRecurrence.lean)
and `pointwiseErgodicTheorem_of_external_inputs` in
[MainPointwise](../PSPrimes/MainPointwise.lean), then their specifications in
[Definitions](../PSPrimes/Definitions.lean). The external-input boundary and
unformalized translations are recorded in [ASSUMPTIONS.md](ASSUMPTIONS.md).

## 1. Common definitions and exact algebra

Start with **Definitions**: the actual PS set, von Mangoldt weights, integer
polynomial family, configurations with distinct terms, integer actions and
normalized averages. [Rescaling](../PSPrimes/Rescaling.lean) defines the integer
polynomial P(Qy)/Q by its coefficients and proves the exact evaluation,
degree and nested-rescaling identities.

The finite forms and phase-bound conventions are in
[Counting](../PSPrimes/Counting.lean) and
[PhaseBounds](../PSPrimes/PhaseBounds.lean). Recurrence-specific notation,
coefficient bounds and affine transport are grouped in `RecurrenceDefinitions`,
`RecurrenceAlgebra` and `ConfigurationTransport`. These support the same
configurations throughout; they do not substitute a simpler polynomial model.

## 2. Finite comparison with ordinary-prime weights

The destination is `ps_counting_comparison` in
[FinalComparison](../PSPrimes/FinalComparison.lean), the original
Proposition 2.3 with degree-only range and saving, the exact natural floor
scale, and an implied constant chosen before the subpower exponent a.

Read [Progressions](../PSPrimes/Progressions.lean) for the checked Fourier
restriction of polynomial phases, then [Lifting](../PSPrimes/Lifting.lean)
for the two-variable change of variables restoring the fixed family P.
`Homogeneity` and `Comparison` supply the finite bound. `PowerSaving` performs
the quantitative absorption; `Scales`, `Asymptotics` and `AsymptoticScales`
handle exact floors and uniform thresholds. These auxiliary modules form one
comparison argument. The deep arithmetic and VN estimates are the predicates
in [ExternalInputs](../PSPrimes/ExternalInputs.lean).

## 3. Quantitative recurrence

Read the final assembly in **MainRecurrence** and the actual finite-set
construction in [RecurrenceConstruction](../PSPrimes/RecurrenceConstruction.lean).
The latter extends only already verified prefixes, preserves the forbidden
configuration and smoothness invariants, and derives the contradiction from
multiplicative density growth. `FiniteConstruction` records a separate generic
prefix-extension lemma; the actual set-prefix argument is implemented in
`RecurrenceConstruction`.

There are three focused routes into this argument:

- **The density increment:** [DensityIncrement](../PSPrimes/DensityIncrement.lean)
  applies the separate source comparison and regularity interfaces to actual
  local factors. `Density` contains the equal-mass and product-telescoping
  argument. `KMTTNormalization` and `NormalizedDensityIncrement` implement the
  permitted normalization of the positive length prefactor. The quoted source
  data are in `KMTTInterfaces`.
- **Why absence creates a discrepancy:**
  [FinalPrimeDiscrepancy](../PSPrimes/FinalPrimeDiscrepancy.lean) combines the
  actual set count, model overlap, collisions, higher prime powers and
  quantitative comparison. `PrimeDiscrepancy`, `ModelOverlap`,
  `PolynomialBounds`, `ExceptionalTerms`, `PrimePowers` and `DiscrepancySaving`
  are its finite and asymptotic supporting pieces. `PrimeMassInputs` records
  the compatible classical prime-progression mass input; `SmallScale` excludes
  the source regularity alternative in the admitted range.
- **Why the iteration stays admissible:**
  [FiniteIterationBounds](../PSPrimes/FiniteIterationBounds.lean) derives the
  accumulated bounds from the actual one-step logarithmic recurrences and
  chooses a threshold before the initial density and every stage. `Iteration`,
  `RecurrenceIteration` and `LogScales` provide its finite recurrence,
  asymptotic and floor-scale calculations. `InitialProgression` and
  `SmoothModuli` retain the full initial residue intersection and fixed lcm
  smoothness parameter.

## 4. Pointwise comparison and weight removal

The destination is **MainPointwise**, for the actual normalized PS-prime and
ordinary-prime averages with one common a.e. limit. Its analytic comparison is
[OrbitComparison](../PSPrimes/OrbitComparison.lean), which derives the L1 saving
and applies the full-sequence a.e. comparison. The quoted orbit, PNT and
ordinary-prime convergence inputs are in [OrbitInputs](../PSPrimes/OrbitInputs.lean).

[Pointwise](../PSPrimes/Pointwise.lean) contains the original discrete Abel
argument, positive-weight unweighting, integer-power subsequence, Tonelli
passage, weighted interpolation and actual selected-set enumeration.
[Representatives](../PSPrimes/Representatives.lean) transfers a.e. statements
to bounded representatives along all integer iterates and restores the
manuscript's essential L∞ hypotheses. The shared `PrimePowers` estimates
justify removing nonprime von Mangoldt support.

For reproducibility and current build evidence, use the README and
`scripts/check.sh`. Module membership alone is not a verification claim;
the statement map, assumption catalogue and actual audit logs record that
distinction.
