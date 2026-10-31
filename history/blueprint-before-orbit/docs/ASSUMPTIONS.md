# External assumptions and source-formulation bridges

All seven original numbered deductions are checked **conditionally**. Theorem 1.1 is `quantitative_recurrence`; Theorem 1.2 is `pointwiseErgodicTheorem_of_external_inputs`. The external analytic and arithmetic inputs remain unproved and uninstantiated. No mathematical axiom was added, and no input assumes an original conclusion of this manuscript.

There are eight named external predicates. The two main theorems jointly use seven of them: the standalone `KMTTUnweightedInput` is replaced, in Theorem 1.1, by the stronger *explicitly catalogued joint selection* `KMTTCompatibleInput`. This distinction matters: separate existential witnesses need not have the same comparison constant.

| Catalogue entry / actual predicate | Conclusions using it |
| --- | --- |
| SS — `ShaoSunPhaseInput` | Lemma 2.2; Proposition 2.3; Lemma 3.2; Theorem 1.1; Proposition 4.1; Theorem 1.2 |
| TV — `FiniteVNInput` | Proposition 2.3; Lemma 3.2; Theorem 1.1 |
| OR — `OrbitVNInput` | Proposition 4.1; Theorem 1.2 |
| PNT — `PrimeNumberTheoremInput` | Proposition 4.1; Theorem 1.2 |
| MW — `OrdinaryPrimePointwiseInput` | Theorem 1.2 |
| KM-U — `KMTTUnweightedInput` | Standalone Proposition 3.1; its content is supplied through KM-Compatible in Theorem 1.1 |
| KM-R — `KMTTRegularityInput` | Proposition 3.1; Theorem 1.1 |
| KM-Compatible — `KMTTCompatibleInput` | Theorem 1.1; supplies the same-parameter KM-M data used by Lemma 3.2 |

Thus the exact public main-theorem premises are:

```lean
quantitative_recurrence
  (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
  (hReg : KMTTRegularityInput) (hJoint : KMTTCompatibleInput)
  (P : PolynomialFamily ℓ) : QuantitativeRecurrence P
```

```lean
pointwiseErgodicTheorem_of_external_inputs
  (hSS : ShaoSunPhaseInput) (hOR : OrbitVNInput)
  (hPNT : PrimeNumberTheoremInput) (hMW : OrdinaryPrimePointwiseInput)
  (P : PolynomialFamily ℓ) : PointwiseErgodicTheorem P
```

Source interfaces: [ExternalInputs.lean](../PSPrimes/ExternalInputs.lean), [OrbitInputs.lean](../PSPrimes/OrbitInputs.lean), [KMTTInterfaces.lean](../PSPrimes/KMTTInterfaces.lean), and [PrimeMassInputs.lean](../PSPrimes/PrimeMassInputs.lean).

The second displayed signature suppresses its universe argument and ordinary implicit parameters. The source contains the authoritative elaborated statements. The verbatim interface declarations below are in namespace `PSPrimes`, with imports and opened namespaces as in their linked source files; they are not standalone Lean modules.

## SS: polynomial-phase discorrelation

Primary reference: Shao–Sun, [arXiv:2605.18676v1](https://arxiv.org/html/2605.18676v1), **unnumbered polynomial-phase corollary immediately after Theorem 2.1**. The corollary is stated in the published source; the project does not require an additional unproved circle construction to quote it. Definition 4.5 explains the optional general nilsequence argument.

For a fixed degree bound, the gamma range and positive saving precede gamma; the constant precedes the cutoff and every real phase coefficient. The actual weight is `sparseMangoldt γ − vonMangoldt`. No coefficient restriction is imposed.

```lean
def ShaoSunPhaseInput : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∃ σ : ℝ, 0 < σ ∧ ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        PhaseBound r X (fun n => (discrepancyWeight γ n : ℂ))
          (C * (X : ℝ) ^ (1 - σ))
```
**External translation SS-finiteX:** integer cutoffs, the degree-bound specialization, and extension of the published `X≥3` estimate to `X=1,2` by enlarging a gamma-dependent constant. That finite extension has not separately been proved in Lean. The general nilsequence theorem is unformalized optional background.

**Checked applications:** exact Fourier projection and endpoint shift give `progressionPhase_of_shaoSun`, including `Q=1`; the saving is decreased to `min(σ,1/2)`. All finite-comparison, orbit-comparison and mass applications to the actual discrepancy are checked.

## TV: fixed-family finite generalized von Neumann estimate

Primary reference: Teräväinen, [arXiv:2401.03174v2](https://arxiv.org/html/2401.03174v2), Theorem 4.1. The exponent is selected from the maximum degree before the family. The implied constant can depend on the entire fixed family and support constant. The source is not assumed coefficient-uniform over rescaled families.

```lean
def FiniteVNInput : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ K : ℕ, 1 ≤ K ∧
    ∀ (ℓ : ℕ) (R : Fin ℓ → Polynomial ℤ),
      0 < ℓ → StrictMono (fun i => (R i).natDegree) →
      (∀ i, 1 ≤ (R i).natDegree) →
      (∀ i, (R i).natDegree ≤ d) → (∃ i, (R i).natDegree = d) →
      ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
        ∀ M : ℕ, 1 ≤ M → ∀ (θ : ℕ → ℂ) (f₀ : ℤ →₀ ℂ)
          (f : Fin ℓ → ℤ → ℂ) (E : ℝ),
          (∀ n ∈ initialInterval M, ‖θ n‖ ≤ 1) →
          (∀ x, ‖f₀ x‖ ≤ 1) → (∀ i x, ‖f i x‖ ≤ 1) →
          (∀ x : ℤ, C₀ * (M : ℝ) ^ d < |(x : ℝ)| → f₀ x = 0) →
          (∀ i (x : ℤ), C₀ * (M : ℝ) ^ d < |(x : ℝ)| → f i x = 0) →
          0 ≤ E → PhaseBound d M θ ((M : ℝ) * E) →
          ‖polynomialForm M d R θ f₀ f‖ ≤
            C * ((M : ℝ)⁻¹ + E) ^ (1 / (K : ℝ))
```
**External translation TV-B:** the published `u^(d+1)` supremum is represented by an arbitrary nonnegative bound on every normalized phase correlation. Supremum boundedness, phase-sign closure and monotonicity justify this mathematically; their equivalence with `PhaseBound` is not formalized. Integer cutoffs and positive-degree families are explicit application specializations.

**Checked applications:** magnitude scaling, bounded-support-to-finitely-supported representation, exact fixed-family dilation, support transport, the `Q²` normalization loss, logarithmic envelopes and quantified uniform thresholds. `ps_counting_comparison` proves the full original Proposition 2.3; it does not assume that comparison as a separate input.

## OR: orbit L¹ estimate

Primary reference: Mousavi, [arXiv:2609.01847v1](https://arxiv.org/html/2609.01847v1), Proposition 1.4, displayed (8), (10). This separately quoted earlier estimate is the ergodic branch's analytic input; TV is not an extra premise of that branch. The conjunction below includes actual integrability, so an undefined-integral convention cannot supply the inequality.

```lean
def OrbitVNInput : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ K : ℕ, 1 ≤ K ∧
    ∀ (ℓ : ℕ) (P : Fin ℓ → Polynomial ℤ),
      0 < ℓ → StrictMono (fun i => (P i).natDegree) →
      (∀ i, 1 ≤ (P i).natDegree) →
      (∀ i, (P i).natDegree ≤ d) → (∃ i, (P i).natDegree = d) →
      ∃ C : ℝ, 0 < C ∧
        ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
          ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
            (∀ i, AEStronglyMeasurable (f i) μ) →
            (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) →
            ∀ N : ℕ, 1 ≤ N → ∀ (g : ℕ → ℝ) (B E : ℝ),
              0 < B → 0 ≤ E →
              (∀ n ∈ initialInterval N, |g n| ≤ B) →
              PhaseBound d N (fun n => (g n : ℂ)) ((N : ℝ) * E) →
              Integrable (fun x => weightedAverage g (fun n => orbitProduct P T f n x) N) μ ∧
                (∫ x, ‖weightedAverage g (fun n => orbitProduct P T f n x) N‖ ∂μ) ≤
                  C * B * ((N : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ))
```
**External translation OR-B:** real weights, probability-space and essentially 1-bounded specialization; the shifted family `P_i(n−1)` and integer-action formulation; the every-phase/supremum translation and finite-average integrability. The earlier duality/transference proof is quoted, not reconstructed from TV.

**Checked applications:** simultaneous bounded representatives at every integer iterate, congruence through almost-everywhere changes, normalization, discrepancy power saving, explicit polynomial cutoffs, summability and full-sequence interpolation. `ps_orbit_comparison` proves Proposition 4.1 from SS, OR and PNT.

## PNT: the ordinary von Mangoldt mass limit

Primary reference: Terence Tao, [246B Notes 4: The Riemann zeta function and the prime number theorem](https://terrytao.wordpress.com/2021/02/12/246b-notes-4-the-riemann-zeta-function-and-the-prime-number-theorem/), 12 February 2021, **Theorem 6 (von Mangoldt form)**. It directly states the normalized Chebyshev-psi limit. Integer-cutoff specialization is included externally; no prime-counting-to-weighted conversion is silently assumed.

```lean
def PrimeNumberTheoremInput : Prop :=
  Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
    ∑ n ∈ initialInterval N, ArithmeticFunction.vonMangoldt n) atTop (𝓝 1)
```
The pinned Mathlib search did not furnish this exact prime number theorem. It supplies the arithmetic functions and elementary prime-power infrastructure. Actual sparse mass, higher-prime-power removal and both prime-counting unweighting applications are proved internally.

## MW: ordinary weighted almost-everywhere convergence

Primary reference: Mirek–Wan–Wright, [arXiv:2505.15549v2](https://arxiv.org/html/2505.15549v2), Theorem 1.1(ii). Its published conclusion is already von Mangoldt-weighted convergence for distinct-degree integer polynomials, with finite `1<q_i<∞` and `Σ1/q_i≤1`.

```lean
def OrdinaryPrimePointwiseInput : Prop :=
  ∀ (ℓ : ℕ) (P : Fin ℓ → Polynomial ℤ),
    0 < ℓ → StrictMono (fun i => (P i).natDegree) →
    (∀ i, 1 ≤ (P i).natDegree) →
    ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
        (∀ i, AEStronglyMeasurable (f i) μ) →
        (∀ i, ∃ C : ℝ, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C) →
        ∃ L : X → ℂ, ∀ᵐ x ∂μ,
          Tendsto (fun N : ℕ => weightedAverage ArithmeticFunction.vonMangoldt
            (fun n => orbitProduct P T f n x) N) atTop (𝓝 (L x))
```
**External translation MW-B:** on a probability space, bounded inputs belong to `L^(2ℓ)`; the source's finite-exponent hypothesis is not silently replaced by an unproved endpoint theorem. The integer-action and polynomial-shift specialization are also included externally. Constants in the polynomials are allowed by the source. The project has not separately proved these source-to-interface steps.

**Checked applications:** actual prime-power residuals are removed after invoking weighted convergence; positive monotone weight conditions and mass limits are proved; discrete Abel summation, infinitude, the `Nat.nth` enumeration and transfer to actual prime cutoffs give the common limit in Theorem 1.2. Its final input functions need only be essentially bounded and almost-everywhere strongly measurable.

## KM-U: unweighted discrepancy at a slightly shorter scale

Primary reference: Krause–Mousavi–Tao–Teräväinen (KMTT), [arXiv:2608.19525v1](https://arxiv.org/html/2608.19525v1), Proposition 5.2, (5.9)–(5.12); parameter choices (5.7)–(5.8) and (5.35)–(5.36). The source's `k` is this project's `ℓ+1`.

The source parameter record and admissibility predicate retain all varying density, smoothness and scale conditions:

```lean
structure KMTTComparisonParameters (ℓ Adiv : ℕ) where
  C₁ : ℝ
  K₁ : ℝ
  c₀ : ℝ
  c₁ : ℝ
  C₁_ge : 2 ≤ C₁
  K₁_ge : 2 ≤ K₁
  c₀_pos : 0 < c₀
  c₀_lt : c₀ < 1 / 2
  c₁_pos : 0 < c₁
  c₁_le : c₁ ≤ 1
  divisibility_exponent : (3 * (ℓ + 1) * Adiv : ℝ) ≤ C₁
  divisibility_constant : (16 / c₁) ^ Adiv + 1 ≤ K₁
```
```lean
def KMTTAdmissible {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    (N Q s : ℕ) (δ : ℝ) : Prop :=
  1 ≤ Q ∧ 2 ≤ s ∧
  (Real.log N) ^ (-(1 / p.C₁ ^ 2)) < δ ∧ δ ≤ 1 ∧
  ⌈p.K₁ * δ ^ (-p.C₁)⌉₊ ≤ s ∧ (s : ℝ) ≤ (Real.log N) ^ p.c₀ ∧
  (Q : ℝ) ≤ Real.exp ((Real.log N) ^ (2 * p.c₀)) ∧
  SmoothUpTo s Q ∧ smoothModulus s ∣ Q
```
```lean
def KMTTUnweightedWitness (C : ℝ) (d ℓ Adiv : ℕ)
    (p : KMTTComparisonParameters ℓ Adiv) : Prop :=
  ∃ Nmin : ℕ, ∀ N : ℕ, Nmin ≤ N → ∀ Q s : ℕ, ∀ δ : ℝ,
    KMTTAdmissible p N Q s δ →
    ∀ R : PolynomialFamily ℓ,
      (∀ i, HasCQCoefficients C Q (R.polynomials i)) →
      (∀ i, (R.polynomials i).natDegree ≤ d) →
      (∃ i, (R.polynomials i).natDegree = d) →
      ∀ A : Finset ℤ, A ⊆ integerInterval N → (A.card : ℝ) = δ * N →
      p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) ≤
        |realSetCount N (floorScale N Q d) Q R.polynomials ArithmeticFunction.vonMangoldt A -
          realModelCount N (floorScale N Q d) Q R.polynomials ArithmeticFunction.vonMangoldt δ| →
      ∃ M₀ : ℕ,
        ⌈(floorScale N Q d : ℝ) *
          Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ)))⌉₊ ≤ M₀ ∧
        M₀ ≤ floorScale N Q d ∧
        p.c₁ * δ ^ (ℓ + 1) / 4 ≤
          |realSetCount N M₀ Q R.polynomials (fun _ => 1) A -
            realModelCount N M₀ Q R.polynomials (fun _ => 1) δ|
```
```lean
def KMTTUnweightedInput : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ d ℓ : ℕ, 1 ≤ d → 1 ≤ ℓ → ∀ Adiv : ℕ,
    ∃ p : KMTTComparisonParameters ℓ Adiv, KMTTUnweightedWitness C d ℓ Adiv p
```
**External translation KM-U-B:** real indicator counts, finite positive integer cutoffs, the exact finite-form normalization and the source-to-Lean support identification. Constants are chosen once, not separately for each density or modulus. The source permits increasing the compatibility constants; no statement uniform over arbitrary coefficient families beyond its `(C,Q)` hypotheses is added.

**Checked application:** `kmtt_density_increment_normalized` combines this discrepancy with KM-R, the original equal-mass/telescoping argument, actual progression atoms, divisibility and elimination of the small-scale branch. The literal length bound has coefficient one. Its normalization increases `K₁` and one inverse-modulus exponent; the relevant witness restriction is proved in `KMTTNormalization.lean`. This proved restriction does not constitute the unproved KM-J bridge below.

## KM-R: weak regularity, including the small-scale alternative

Primary reference: KMTT Lemma 5.3, (5.25)–(5.28). `coordinateDegrees R 0` is the smallest positive degree, not zero; coordinate `i+1` has the degree of `R_i`. Resolution means the **number of points** of an atom, not its diameter. Every atom is an actual arithmetic progression, the atoms partition all `[N]`, and the projected function is its atomwise mean extended by zero.

```lean
structure KMTTRegularityWitness (C : ℝ) (d ℓ Bmax Aq Aε T : ℕ) where
  Adiv : ℕ
  Adiv_pos : 1 ≤ Adiv
  smallConstant : ℝ
  smallConstant_pos : 0 < smallConstant
  resolutionConstant : ℝ
  resolutionConstant_pos : 0 < resolutionConstant
  regularity : ∀ N Q M₀ : ℕ, 1 ≤ N → 1 ≤ Q → 1 ≤ M₀ →
    (M₀ : ℝ) ≤ rootScale N Q d →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      smoothModulus ⌈ε ^ (-(Adiv : ℝ))⌉₊ ∣ Q →
      ∀ R : PolynomialFamily ℓ,
        (∀ i, HasCQCoefficients C Q (R.polynomials i)) →
        (∀ i, (R.polynomials i).natDegree ≤ d) →
        (∃ i, (R.polynomials i).natDegree = d) →
        ∀ f : Fin (ℓ + 1) → ℤ → ℝ,
          (∀ i x, |f i x| ≤ 1) →
          (∀ i x, x ∉ integerInterval N → f i x = 0) →
          ((M₀ : ℝ) ≤ smallConstant * ((Q : ℝ) / ε) ^ T) ∨
          ∃ b : ℕ, 1 ≤ b ∧ b ≤ Bmax ∧
            ∃ factors : Fin (ℓ + 1) → ArithmeticLocalFactor N (Q ^ b),
            ∃ F : Fin (ℓ + 1) → ℤ → ℝ,
              (∀ i, IsLocalProjection (factors i) (f i) (F i)) ∧
              (∀ i, resolutionConstant * (Q : ℝ) ^ (-(Aq : ℝ)) * ε ^ Aε *
                (M₀ : ℝ) ^ coordinateDegrees R i ≤ (factors i).resolution) ∧
              |realConfigurationForm N M₀ Q R.polynomials (fun _ => 1) f -
                realConfigurationForm N M₀ Q R.polynomials (fun _ => 1) F| ≤ ε
```
```lean
def KMTTRegularityInput : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ Bmax : ℕ, 1 ≤ Bmax ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ Aq Aε T : ℕ, 1 ≤ Aq ∧ 1 ≤ Aε ∧ 1 ≤ T ∧
      ∀ C : ℝ, 1 ≤ C → Nonempty (KMTTRegularityWitness C d ℓ Bmax Aq Aε T)
```
**External translation KM-R-B:** finite arithmetic-progression partition and real-observable formulation; explicit positive implicit constants and natural exponents unpacking the source's O-notation; the natural divisibility exponent and cutoff convention. Exponents depending only on degree and length are selected before `C`, whereas positive prefactors may depend on `C`. The retained small-scale alternative is excluded by a proved uniform argument in `SmallScale.lean`, not by an assumption.

## KM-M and KM-J: compatible prime mass and joint parameter selection

Primary source facts: KMTT Lemma 5.1 proof, **(5.2), (5.4)**, and **(5.15)**; Proposition 5.2 proof and constant choices **(5.7)–(5.8), (5.23)–(5.24), (5.35)–(5.36)**. See [KMTT_INPUTS_WORKING.md](KMTT_INPUTS_WORKING.md) for the source-byte hashes, exact transcription and two independent proof-level reviews.

The finite discrepancy lemma takes the following **explicit same-parameter data**. Its cutoff is fixed before scale, density and modulus; no uniform mass fraction as the cutoff tends to zero is claimed.

```lean
structure PrimeProgressionMassWitness {ℓ Adiv : ℕ}
    (p : KMTTComparisonParameters ℓ Adiv) (d : ℕ) (τmax : ℝ) where
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  cutoff_le_one : cutoff ≤ 1
  cutoff_le : cutoff ≤ τmax
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  exponentConstant : ℝ
  exponentConstant_pos : 0 < exponentConstant
  threshold : ℕ
  truncated_mass : ∀ N Q s : ℕ, ∀ δ : ℝ,
    threshold ≤ N → KMTTAdmissible p N Q s δ →
    (4 * p.c₁) *
      (∑ y ∈ initialInterval (floorScale N Q d), ArithmeticFunction.vonMangoldt (Q * y + 1)) ≤
      ∑ y ∈ initialInterval ⌊cutoff * (floorScale N Q d : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt (Q * y + 1)
  full_mass : ∀ N Q s : ℕ, ∀ δ : ℝ,
    threshold ≤ N → KMTTAdmissible p N Q s δ →
    lowerConstant * Real.exp (-exponentConstant * (Real.log N) ^ (2 * p.c₀)) ≤
      primeProgressionMass Q (floorScale N Q d)
```
The recurrence theorem requires this *joint* selector, rather than assuming that separately chosen existential records coincide:

```lean
def KMTTCompatibleInput : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ d ℓ : ℕ, 1 ≤ d → 1 ≤ ℓ → ∀ Adiv : ℕ,
    ∀ τmax : ℝ, 0 < τmax →
      ∃ p : KMTTComparisonParameters ℓ Adiv,
        KMTTUnweightedWitness C d ℓ Adiv p ∧
        Nonempty (PrimeProgressionMassWitness p d τmax)
```
**External bridge KM-J:** choose the source's sufficiently small fixed cutoff additionally below `τmax`; (5.2) gives a fixed positive mass fraction. Choose `c₁` smaller than one quarter of that fraction and no larger than a valid Lemma 5.1 constant. Rerun Proposition 5.2's proof with this fixed positive `c₁`, enlarging its constants and thresholds; then choose compatible regularity/divisibility constants. This supports the joint existence mathematically. It is **not** a monotonicity consequence of the already fixed Proposition 5.2: decreasing `c₁` also weakens its hypothesis. No Lean proof of this fixed-cutoff and constant-reselection bridge, or inhabitant of `KMTTCompatibleInput`, is supplied.

The source prints no numerical value for its initial cutoff, so it is not claimed already to satisfy the required `τmax`. The actual selector quantifies positive `τmax` **before** the parameter record. In Theorem 1.1 it is `1/(10*C*(d+1))`, with the fixed coefficient bound `C`; all selected constants therefore have the allowed fixed-parameter dependence. This additional source-to-interface bridge was identified before claiming conditional completion of the recurrence theorem. It does not assume a sparse-prime discrepancy, a dense progression, an admissible iteration, or either original main result.

**Checked applications:** polynomial shifts are at most `N/10` on the actual fixed cutoff; interval overlap, collision roots, actual higher prime powers, the finite comparison and quantified error dominance prove `ps_prime_discrepancy`. The compatible record is passed unchanged to the increment argument. Exact initialization, affine forbidden-configuration transport, finite-prefix construction and uniform current-stage admissibility complete `quantitative_recurrence`.

## What remains external

SS, TV, OR, PNT, MW and the KMTT finite/mass theorems have no proofs or inhabitants in this project. The formulation bridges SS-finiteX, TV-B, OR-B, MW-B, KM-U-B, KM-R-B and KM-J remain external as described above. All seven original numbered deductions are proved under their displayed explicit premises; the two numbered quoted results remain external. No no-Siegel strengthening is used.

An axiom audit records only standard foundational dependencies (`propext`, `Classical.choice`, `Quot.sound`). It does not prove any input predicate true, nor establish statement correspondence. Those are separate mathematical and source-review obligations, documented here and in [PAPER_MAP.md](PAPER_MAP.md). Source modules, the final clean-build record and the actual declaration audit remain the verification authority.
