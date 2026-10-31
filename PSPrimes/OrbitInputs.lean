import PSPrimes.PhaseBounds

/-!
# Analytic input specifications and the derived orbit bound

These predicates add no mathematical axioms. `OrbitVNInput` is retained as
an exact specification for arbitrary real weights; it is proved from
`FiniteVNInput` by `orbitVNInput_of_finiteVNInput` in `OrbitTransference.lean`
and is no longer an independent external premise of the pointwise argument.
That proof checks the integer polynomial shift, exact spatial cutoffs,
normalization, integrability, essential bounds and probability-system
transference from Proposition 1.4 of the related supplied manuscript.

PNT and the Mirek--Wan--Wright bounded probability-space specialization
remain external. The latter's finite-Lq embedding and polynomial-shift
source translation are recorded in `docs/ASSUMPTIONS.md`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

universe u

namespace PSPrimes

/-- Orbit generalized von Neumann specification, for arbitrary real weights.
It is derived from `FiniteVNInput` in `OrbitTransference.lean`.

The exponent `K` is selected from `d` before the family. The constant `C` is
selected after the entire fixed family and before the system, functions,
cutoff, weight, magnitude bound, and phase bound. `E` bounds every normalized
polynomial-phase correlation: the unnormalized `PhaseBound` is `N*E`.
All surrounding hypotheses, including essential boundedness, are explicit.
The conjunction includes integrability so the real integral cannot become
an undefined-integral convention in an application.
-/
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

/-- Ordinary PNT in exactly the normalized von Mangoldt mass formulation used
by equation `e:weight-mass`. This predicate does not quote a prime-count
asymptotic and silently perform partial summation. -/
def PrimeNumberTheoremInput : Prop :=
  Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
    ∑ n ∈ initialInterval N, ArithmeticFunction.vonMangoldt n) atTop (𝓝 1)

/-- Explicitly external L∞ probability-space specialization of
Mirek--Wan--Wright Theorem 1.1(ii), for the actual von Mangoldt-weighted
averages and integer actions. Constant coefficients of the fixed family are
allowed; positivity and strict increase of the degrees are required.

The essential-bound quantifier admits all bounded representatives, rather
than silently replacing the manuscript's L∞ hypothesis by a pointwise bound.
The unformalized L∞-to-finite-Lq and shift bridges belong to this named
specialization, not to any proved application theorem.
-/
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

end PSPrimes
