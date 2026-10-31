import PSPrimes.ExternalInputs

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- Homogeneity step (8). `hVN` is the fixed-family instance of the external
finite von Neumann estimate, not a hypothesis about the target PS weight.
All spatial functions and their support conditions are fixed in this instance. -/
theorem homogeneous_polynomialForm_bound {ℓ : ℕ}
    (M d K : ℕ) (R : Fin ℓ → Polynomial ℤ) (f₀ : ℤ →₀ ℂ)
    (f : Fin ℓ → ℤ → ℂ) (C : ℝ)
    (hVN : ∀ (θ : ℕ → ℂ) (E : ℝ),
      (∀ n ∈ initialInterval M, ‖θ n‖ ≤ 1) →
      0 ≤ E → PhaseBound d M θ ((M : ℝ) * E) →
      ‖polynomialForm M d R θ f₀ f‖ ≤
        C * ((M : ℝ)⁻¹ + E) ^ (1 / (K : ℝ)))
    (B E : ℝ) (hB : 0 < B) (hE : 0 ≤ E) (w : ℕ → ℂ)
    (hw : ∀ n ∈ initialInterval M, ‖w n‖ ≤ B)
    (hphase : PhaseBound d M w ((M : ℝ) * E)) :
    ‖polynomialForm M d R w f₀ f‖ ≤
      B * C * ((M : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ)) := by
  let θ : ℕ → ℂ := fun n => (B : ℂ)⁻¹ * w n
  have hnorm : ‖(B : ℂ)⁻¹‖ = B⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  have hθ : ∀ n ∈ initialInterval M, ‖θ n‖ ≤ 1 := by
    intro n hn
    dsimp [θ]
    rw [norm_mul, hnorm]
    calc
      B⁻¹ * ‖w n‖ ≤ B⁻¹ * B :=
        mul_le_mul_of_nonneg_left (hw n hn) (inv_nonneg.mpr hB.le)
      _ = 1 := inv_mul_cancel₀ hB.ne'
  have hθphase : PhaseBound d M θ ((M : ℝ) * (E / B)) := by
    have hp := hphase.smul (B : ℂ)⁻¹
    rw [hnorm] at hp
    convert hp using 1
    dsimp [θ]
    ring
  have hbound := hVN θ (E / B) hθ (div_nonneg hE hB.le) hθphase
  have hid : polynomialForm M d R w f₀ f =
      (B : ℂ) * polynomialForm M d R θ f₀ f := by
    rw [← polynomialForm_smul]
    congr 1
    funext n
    dsimp [θ]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hB.ne'), one_mul]
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  exact (mul_le_mul_of_nonneg_left hbound hB.le).trans_eq (by ring)

end PSPrimes
