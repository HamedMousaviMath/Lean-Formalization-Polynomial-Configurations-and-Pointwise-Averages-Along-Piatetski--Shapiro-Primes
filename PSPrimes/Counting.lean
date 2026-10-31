import PSPrimes.Definitions

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- Every spatial function in the manuscript's bounded support interval has
an exactly equal finitely supported representative. No values are truncated. -/
theorem exists_finsupp_of_bounded_support (g : ℤ → ℂ) (R : ℝ)
    (hg : ∀ x : ℤ, R < |(x : ℝ)| → g x = 0) :
    ∃ f₀ : ℤ →₀ ℂ, ∀ x, f₀ x = g x := by
  classical
  let s : Finset ℤ := Finset.Icc (-⌈R⌉) ⌈R⌉
  have hs : ∀ x, g x ≠ 0 → x ∈ s := by
    intro x hx
    have hbound : |(x : ℝ)| ≤ R := le_of_not_gt (fun h => hx (hg x h))
    have hceil : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
    have habs := abs_le.mp (hbound.trans hceil)
    apply Finset.mem_Icc.mpr
    exact_mod_cast habs
  exact ⟨Finsupp.onFinset s g hs, fun _ => rfl⟩

/-- Equation (12) as a finite sum. Finite support of f₀ makes the unrestricted
integer sum exact, regardless of the supports of the remaining functions. -/
def countingForm {ℓ : ℕ} (N M Q : ℕ) (R : Fin ℓ → Polynomial ℤ)
    (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) : ℂ :=
  ((N : ℂ) * (M : ℂ))⁻¹ *
    ∑ x ∈ f₀.support, ∑ y ∈ initialInterval M,
      w (Q * y + 1) * f₀ x * ∏ i, f i (x + (R i).eval (y : ℤ))

theorem countingForm_sub {ℓ : ℕ} (N M Q : ℕ) (R : Fin ℓ → Polynomial ℤ)
    (w v : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) :
    countingForm N M Q R (fun n => w n - v n) f₀ f =
      countingForm N M Q R w f₀ f - countingForm N M Q R v f₀ f := by
  simp only [countingForm, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem countingForm_smul {ℓ : ℕ} (N M Q : ℕ) (R : Fin ℓ → Polynomial ℤ)
    (a : ℂ) (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) :
    countingForm N M Q R (fun n => a * w n) f₀ f =
      a * countingForm N M Q R w f₀ f := by
  simp only [countingForm, mul_assoc, ← Finset.mul_sum]
  ring

/-- The exact subtraction identity used before (27), with the sign fixed. -/
theorem countingForm_discrepancy {ℓ : ℕ} (N M Q : ℕ) (R : Fin ℓ → Polynomial ℤ)
    (γ : ℝ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) :
    countingForm N M Q R (fun n => (discrepancyWeight γ n : ℂ)) f₀ f =
      countingForm N M Q R (fun n => (sparseMangoldt γ n : ℂ)) f₀ f -
      countingForm N M Q R (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) f₀ f := by
  simpa only [discrepancyWeight, Complex.ofReal_sub] using
    countingForm_sub N M Q R (fun n => (sparseMangoldt γ n : ℂ))
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) f₀ f

/-- Elementary discrepancy deduction, retaining explicit quantitative errors.
It is only the last subtraction step of Lemma 3.2, not that lemma itself. -/
theorem model_minus_count {model count mass δ c err : ℝ}
    (hmodel : (2 * c) * δ * mass ≤ model)
    (hcount : count ≤ err) (herr : err ≤ c * δ * mass) :
    c * δ * mass ≤ model - count := by
  nlinarith

end PSPrimes
