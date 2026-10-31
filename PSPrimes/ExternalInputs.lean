import PSPrimes.PhaseBounds

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-!
These are explicit, uninstantiated external hypotheses. They add NO axioms.
No proof of a main result is obtained by assuming that main result.
See docs/ASSUMPTIONS.md for exact provenance and the unformalized bridges.
-/

/-- The published polynomial-phase consequence of Shao--Sun Theorem 2.1.
Saving and gamma range are chosen before gamma; the implied constant is
chosen after gamma and before X and the phase coefficients. -/
def ShaoSunPhaseInput : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∃ σ : ℝ, 0 < σ ∧ ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        PhaseBound r X (fun n => (discrepancyWeight γ n : ℂ))
          (C * (X : ℝ) ^ (1 - σ))

/-- Teräväinen Theorem 4.1 in a bound-for-every-phase formulation.
The exponent K is uniform in families of fixed maximum degree d.
The constant C may depend on the entire fixed polynomial family and C₀.
All functions have the spatial support required by the published result. -/
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

end PSPrimes
