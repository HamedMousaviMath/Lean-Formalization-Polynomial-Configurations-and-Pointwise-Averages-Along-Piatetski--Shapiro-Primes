import PSPrimes.Definitions

noncomputable section
open scoped BigOperators

namespace PSPrimes

def complexPhase (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

@[simp] theorem norm_complexPhase (t : ℝ) : ‖complexPhase t‖ = 1 := by
  simp [complexPhase, Complex.norm_exp]

def phaseSum (M : ℕ) (w : ℕ → ℂ) (φ : Polynomial ℝ) : ℂ :=
  ∑ n ∈ initialInterval M, w n * complexPhase (φ.eval (n : ℝ))

/-- A bound on every phase, rather than a potentially unbounded supremum.
It is the unnormalized version of (6). No coefficient bound is imposed. -/
def PhaseBound (r M : ℕ) (w : ℕ → ℂ) (E : ℝ) : Prop :=
  ∀ φ : Polynomial ℝ, φ.natDegree ≤ r → ‖phaseSum M w φ‖ ≤ E

theorem phaseSum_smul (M : ℕ) (a : ℂ) (w : ℕ → ℂ) (φ : Polynomial ℝ) :
    phaseSum M (fun n => a * w n) φ = a * phaseSum M w φ := by
  simp [phaseSum, mul_assoc, Finset.mul_sum]

theorem PhaseBound.smul {r M : ℕ} {w : ℕ → ℂ} {E : ℝ}
    (h : PhaseBound r M w E) (a : ℂ) :
    PhaseBound r M (fun n => a * w n) (‖a‖ * E) := by
  intro φ hφ
  rw [phaseSum_smul, norm_mul]
  exact mul_le_mul_of_nonneg_left (h φ hφ) (norm_nonneg a)

theorem PhaseBound.mono {r s M : ℕ} {w : ℕ → ℂ} {E : ℝ}
    (h : PhaseBound r M w E) (hs : s ≤ r) : PhaseBound s M w E := by
  intro φ hφ
  exact h φ (hφ.trans hs)

theorem phaseSum_zero (M : ℕ) (w : ℕ → ℂ) :
    phaseSum M w 0 = ∑ n ∈ initialInterval M, w n := by
  simp [phaseSum, complexPhase]

/-- The zero phase gives the total mass discrepancy, a step used in (37). -/
theorem PhaseBound.mass {r M : ℕ} {w : ℕ → ℂ} {E : ℝ}
    (h : PhaseBound r M w E) : ‖∑ n ∈ initialInterval M, w n‖ ≤ E := by
  simpa only [phaseSum_zero] using h 0 (by simp)

def polynomialForm {ℓ : ℕ} (M d : ℕ) (R : Fin ℓ → Polynomial ℤ)
    (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) : ℂ :=
  ((M : ℂ) ^ (d + 1))⁻¹ *
    ∑ x ∈ f₀.support, ∑ n ∈ initialInterval M,
      w n * f₀ x * ∏ i, f i (x + (R i).eval (n : ℤ))

theorem polynomialForm_smul {ℓ : ℕ} (M d : ℕ) (R : Fin ℓ → Polynomial ℤ)
    (a : ℂ) (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) :
    polynomialForm M d R (fun n => a * w n) f₀ f =
      a * polynomialForm M d R w f₀ f := by
  simp only [polynomialForm, mul_assoc, ← Finset.mul_sum]
  ring

/-- Clearing positive denominators makes the saving conditions explicit.
This is the arithmetic of the last display of Proposition 2.3, not its proof. -/
theorem comparison_exponents {ε σ s K : ℝ}
    (hε : 0 ≤ ε) (hs : 0 < s) (hs₁ : s ≤ 1) (hsσ : s ≤ σ)
    (hsmall : 8 * K * ε ≤ s) :
    2 * ε * K - 1 ≤ -s / 2 ∧
      2 * ε * (K - 1) - σ ≤ -s / 2 := by
  constructor <;> nlinarith

end PSPrimes
