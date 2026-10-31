import Mathlib

/-!
# Definitions faithful to Draft1.tex

No existence or convergence assertion in this file is taken as an axiom.
These conclusion predicates are specifications. `MainRecurrence.lean` and
`MainPointwise.lean` establish them under explicit external inputs; this file
does not assert those analytic inputs or unconditional main theorems.
-/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory

universe u

namespace PSPrimes

attribute [local instance] Classical.propDecidable

/-- The positive integer interval used by the manuscript. -/
def initialInterval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- Positive indices only. The value is the natural floor of a real power. -/
def IsPS (c : ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ n = ⌊(k : ℝ) ^ c⌋₊

def IsPSPrime (c : ℝ) (p : ℕ) : Prop := p.Prime ∧ IsPS c p

def sparseMangoldt (γ : ℝ) (n : ℕ) : ℝ :=
  if IsPS (1 / γ) n then
    γ⁻¹ * (n : ℝ) ^ (1 - γ) * ArithmeticFunction.vonMangoldt n
  else 0

def discrepancyWeight (γ : ℝ) (n : ℕ) : ℝ :=
  sparseMangoldt γ n - ArithmeticFunction.vonMangoldt n

@[simp] theorem sparseMangoldt_one (γ : ℝ) : sparseMangoldt γ 1 = 0 := by
  simp [sparseMangoldt]

@[simp] theorem discrepancyWeight_one (γ : ℝ) : discrepancyWeight γ 1 = 0 := by
  simp [discrepancyWeight]

theorem sparseMangoldt_nonneg {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    0 ≤ sparseMangoldt γ n := by
  unfold sparseMangoldt
  split_ifs
  · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ.le)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem sparseMangoldt_prime (γ : ℝ) {p : ℕ} (hp : p.Prime) :
    sparseMangoldt γ p =
      if IsPSPrime (1 / γ) p then γ⁻¹ * (p : ℝ) ^ (1 - γ) * Real.log p else 0 := by
  simp [sparseMangoldt, IsPSPrime, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Equation (1): every polynomial has positive degree and zero constant term. -/
structure PolynomialFamily (ℓ : ℕ) where
  polynomials : Fin ℓ → Polynomial ℤ
  nonempty : 0 < ℓ
  zero_constant : ∀ i, (polynomials i).coeff 0 = 0
  positive_degree : ∀ i, 1 ≤ (polynomials i).natDegree
  increasing_degrees : StrictMono (fun i => (polynomials i).natDegree)

/-- Include P₀ = 0 as the first entry, without a separate polynomial. -/
def pattern {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (x t : ℤ) : Fin (ℓ + 1) → ℤ :=
  Fin.cons x (fun i => x + (P i).eval t)

def ContainsConfiguration {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (c : ℝ) (A : Finset ℤ) : Prop :=
  ∃ (x : ℤ) (p : ℕ), IsPSPrime c p ∧
    (∀ i, pattern P x ((p : ℤ) - 1) i ∈ A) ∧
    Function.Injective (pattern P x ((p : ℤ) - 1))

/-- Theorem 1.1 specification, including the order of c*, κ, c and N₀.
Its conditional proof is `quantitative_recurrence` in `MainRecurrence.lean`. -/
def QuantitativeRecurrence {ℓ : ℕ} (P : PolynomialFamily ℓ) : Prop :=
  ∃ cstar : ℝ, 1 < cstar ∧ ∃ κ : ℝ, 0 < κ ∧
    ∀ c : ℝ, 1 < c → c < cstar →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℤ,
        A ⊆ Finset.Icc 1 (N : ℤ) →
        (N : ℝ) / (Real.log N) ^ κ ≤ (A.card : ℝ) →
        ContainsConfiguration P.polynomials c A

/-- An invertible measurable measure-preserving action; negative polynomial
values are represented by negative integer parameters. -/
structure IntegerAction (X : Type*) [MeasurableSpace X] (μ : Measure X) where
  act : ℤ → X → X
  zero_act : ∀ x, act 0 x = x
  add_act : ∀ n m x, act (n + m) x = act n (act m x)
  preserving : ∀ n, MeasurePreserving (act n) μ μ

def orbitProduct {ℓ : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (P : Fin ℓ → Polynomial ℤ) (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ)
    (n : ℕ) (x : X) : ℂ :=
  ∏ i, f i (T.act ((P i).eval ((n : ℤ) - 1)) x)

def weightedAverage (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ initialInterval N, (w n : ℂ) * z n

def selectedAverage (S : ℕ → Prop) [DecidablePred S] (z : ℕ → ℂ) (N : ℕ) : ℂ :=
  let s := (initialInterval N).filter S
  (s.card : ℂ)⁻¹ * ∑ n ∈ s, z n

/-- Equality of both limits, for the actual prime and PS-prime averages.
Finite zero denominators have the field convention 0; this does not assert
eventual positivity. This definition is a specification, not an axiom. -/
def PointwiseConclusion {ℓ : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (P : Fin ℓ → Polynomial ℤ) (c : ℝ) (T : IntegerAction X μ)
    (f : Fin ℓ → X → ℂ) : Prop :=
  ∃ L : X → ℂ, ∀ᵐ x ∂μ,
    Tendsto (fun N => selectedAverage (IsPSPrime c) (fun n => orbitProduct P T f n x) N)
      atTop (nhds (L x)) ∧
    Tendsto (fun N => selectedAverage Nat.Prime (fun n => orbitProduct P T f n x) N)
      atTop (nhds (L x))

/-- Full Theorem 1.2 specification, including the probability and L∞
hypotheses surrounding the displayed manuscript statement. The conditional
proof is in `MainPointwise.lean`; this definition alone asserts no theorem.
Essential bounds are allowed; they have not been strengthened to everywhere
bounds as an expedient for the orbit estimates. -/
def PointwiseErgodicTheorem {ℓ : ℕ} (P : PolynomialFamily ℓ) : Prop :=
  ∃ cstar : ℝ, 1 < cstar ∧ ∀ c : ℝ, 1 < c → c < cstar →
    ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
        (∀ i, AEStronglyMeasurable (f i) μ) →
        (∀ i, ∃ C : ℝ, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C) →
        PointwiseConclusion P.polynomials c T f

end PSPrimes
