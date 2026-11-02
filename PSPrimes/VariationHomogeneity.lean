import PSPrimes.Variation
import PSPrimes.Representatives

/-!
# Essential L∞ normalization for variation estimates

These results retain the exact product of the essential norms, including
the case in which one of them vanishes.  All orbit equalities are obtained
on a single conull set before the infinite variation is compared.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace PSPrimes

theorem weightedAverage_const_mul (w : ℕ → ℝ) (a : ℂ) (z : ℕ → ℂ) (N : ℕ) :
    weightedAverage w (fun n => a * z n) N = a * weightedAverage w z N := by
  have hsum : (∑ n ∈ initialInterval N, (w n : ℂ) * (a * z n)) =
      a * ∑ n ∈ initialInterval N, (w n : ℂ) * z n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  simp only [weightedAverage, hsum]
  ring

/-- Homogeneity first for explicitly given nonnegative essential bounds.
Zero bounds are allowed, rather than replaced by artificially positive
normalizing constants. -/
theorem orbit_variation_bound_of_oneBounded
    {ℓ : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (P : Fin ℓ → Polynomial ℤ) (T : IntegerAction X μ)
    (w : ℕ → ℝ) (N : ℕ → ℕ) {r : ℝ} (hr : 0 < r) (K : ℝ≥0∞)
    (hunit : ∀ g : Fin ℓ → X → ℂ,
      (∀ i, AEStronglyMeasurable (g i) μ) →
      (∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ 1) →
      (∫⁻ x, rVariation r (fun j =>
        weightedAverage w (fun n => orbitProduct P T g n x) (N j)) ∂μ) ≤ K)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (R : Fin ℓ → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hb : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ R i) :
    (∫⁻ x, rVariation r (fun j =>
      weightedAverage w (fun n => orbitProduct P T f n x) (N j)) ∂μ) ≤
      K * ENNReal.ofReal (∏ i, R i) := by
  classical
  let g : Fin ℓ → X → ℂ := fun i x =>
    if R i = 0 then 0 else (R i : ℂ)⁻¹ * f i x
  have hg (i : Fin ℓ) : AEStronglyMeasurable (g i) μ := by
    by_cases hi : R i = 0
    · simpa [g, hi] using (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : X => (0 : ℂ)) μ)
    · simpa [g, hi] using (hf i).const_mul (R i : ℂ)⁻¹
  have hgb (i : Fin ℓ) : ∀ᵐ x ∂μ, ‖g i x‖ ≤ 1 := by
    by_cases hi : R i = 0
    · simp [g, hi]
    · have hpos : 0 < R i := lt_of_le_of_ne (hR i) (Ne.symm hi)
      filter_upwards [hb i] with x hx
      simp only [g, if_neg hi, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpos]
      calc
        (R i)⁻¹ * ‖f i x‖ ≤ (R i)⁻¹ * R i :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (hR i))
        _ = 1 := inv_mul_cancel₀ hi
  have heq (i : Fin ℓ) : f i =ᵐ[μ] (fun x => (R i : ℂ) * g i x) := by
    filter_upwards [hb i] with x hx
    by_cases hi : R i = 0
    · have hz : f i x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hi] using hx)
        (norm_nonneg _))
      simp [g, hi, hz]
    · have hiC : (R i : ℂ) ≠ 0 := by exact_mod_cast hi
      simp [g, hi, ← mul_assoc, mul_inv_cancel₀ hiC]
  let a : ℂ := ∏ i, (R i : ℂ)
  have hnorm : ‖a‖ₑ = ENNReal.ofReal (∏ i, R i) := by
    rw [← ofReal_norm_eq_enorm]
    congr 1
    dsimp [a]
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hR i)]
  have horbit := ae_orbitProduct_congr P T f
    (fun i x => (R i : ℂ) * g i x) heq
  have hveq : (fun x => rVariation r (fun j =>
      weightedAverage w (fun n => orbitProduct P T f n x) (N j))) =ᵐ[μ]
      (fun x => ‖a‖ₑ * rVariation r (fun j =>
        weightedAverage w (fun n => orbitProduct P T g n x) (N j))) := by
    filter_upwards [horbit] with x hx
    have hseq : (fun j => weightedAverage w (fun n => orbitProduct P T f n x) (N j)) =
        (fun j => a * weightedAverage w (fun n => orbitProduct P T g n x) (N j)) := by
      funext j
      have heqn : (fun n => orbitProduct P T f n x) =
          (fun n => a * orbitProduct P T g n x) := by
        funext n
        rw [hx n, orbitProduct_mul_inputs]
      rw [heqn, weightedAverage_const_mul]
    rw [hseq, rVariation_mul hr]
  rw [lintegral_congr_ae hveq, lintegral_const_mul' _ _ (enorm_ne_top : ‖a‖ₑ ≠ ⊤)]
  calc
    ‖a‖ₑ * (∫⁻ x, rVariation r (fun j =>
      weightedAverage w (fun n => orbitProduct P T g n x) (N j)) ∂μ) ≤ ‖a‖ₑ * K :=
      mul_le_mul_left' (hunit g hg hgb) _
    _ = K * ENNReal.ofReal (∏ i, R i) := by rw [hnorm, mul_comm]

/-- The exact product of the manuscript's essential L∞ norms.  This is a
deduction from the unit estimate, not an additional external hypothesis. -/
theorem orbit_variation_bound_eLpNorm_of_oneBounded
    {ℓ : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (P : Fin ℓ → Polynomial ℤ) (T : IntegerAction X μ)
    (w : ℕ → ℝ) (N : ℕ → ℕ) {r : ℝ} (hr : 0 < r) (K : ℝ≥0∞)
    (hunit : ∀ g : Fin ℓ → X → ℂ,
      (∀ i, AEStronglyMeasurable (g i) μ) →
      (∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ 1) →
      (∫⁻ x, rVariation r (fun j =>
        weightedAverage w (fun n => orbitProduct P T g n x) (N j)) ∂μ) ≤ K)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ) :
    (∫⁻ x, rVariation r (fun j =>
      weightedAverage w (fun n => orbitProduct P T f n x) (N j)) ∂μ) ≤
      K * ∏ i, eLpNorm (f i) ∞ μ := by
  let R : Fin ℓ → ℝ := fun i => (eLpNorm (f i) ∞ μ).toReal
  have hR (i : Fin ℓ) : 0 ≤ R i := ENNReal.toReal_nonneg
  have hb (i : Fin ℓ) : ∀ᵐ x ∂μ, ‖f i x‖ ≤ R i := by
    have hi := enorm_ae_le_eLpNormEssSup (f i) μ
    rw [← eLpNorm_exponent_top] at hi
    filter_upwards [hi] with x hx
    apply (ENNReal.ofReal_le_iff_le_toReal (hf i).eLpNorm_ne_top).mp
    simpa only [ofReal_norm_eq_enorm] using hx
  have h := orbit_variation_bound_of_oneBounded P T w N hr K hunit f
    (fun i => (hf i).aestronglyMeasurable) R hR hb
  have heq : ENNReal.ofReal (∏ i, R i) = ∏ i, eLpNorm (f i) ∞ μ := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hR i)]
    apply Finset.prod_congr rfl
    intro i hi
    exact ENNReal.ofReal_toReal (hf i).eLpNorm_ne_top
  rwa [heq] at h

end PSPrimes
