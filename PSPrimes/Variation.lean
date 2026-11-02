import PSPrimes.Definitions

/-!
# Infinite r-variation and summable perturbations

The seminorm below is the supremum over all finite strictly increasing
chains of indices. Its values lie in the extended nonnegative reals, so
the definition retains infinite variation rather than assigning it zero.
The index starts at zero; shifting the manuscript's indices by one is a
mere reindexing of its sequence.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace PSPrimes

/-- The exact finite-chain expression in the manuscript. A chain of length
zero contributes zero when the exponent is positive. -/
def variationChain (r : ℝ) (a : ℕ → ℂ) (J : ℕ) (j : Fin (J + 1) → ℕ) : ℝ≥0∞ :=
  (∑ h : Fin J, ‖a (j h.succ) - a (j h.castSucc)‖ₑ ^ r) ^ (1 / r)

/-- Each finite-chain value is exactly the nonnegative real expression
printed in the manuscript, embedded in the extended nonnegative reals. -/
theorem variationChain_eq_ofReal {r : ℝ} (hr : 0 ≤ r) (a : ℕ → ℂ)
    (J : ℕ) (j : Fin (J + 1) → ℕ) :
    variationChain r a J j =
      ENNReal.ofReal ((∑ h : Fin J,
        ‖a (j h.succ) - a (j h.castSucc)‖ ^ r) ^ (1 / r)) := by
  unfold variationChain
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _))
    (one_div_nonneg.mpr hr)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)]
  apply Finset.sum_congr rfl
  intro h _
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr, ofReal_norm_eq_enorm]

/-- The true infinite r-variation seminorm, allowing the value infinity. -/
def rVariation (r : ℝ) (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ J : ℕ, ⨆ j : Fin (J + 1) → ℕ,
    if StrictMono j then variationChain r a J j else 0

theorem rVariation_congr (r : ℝ) (a b : ℕ → ℂ) (h : ∀ n, a n = b n) :
    rVariation r a = rVariation r b := by
  congr 1
  exact funext h

theorem ae_rVariation_congr {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (f g : ℕ → X → ℂ)
    (h : ∀ n, f n =ᵐ[μ] g n) :
    (fun x => rVariation r (fun n => f n x)) =ᵐ[μ]
      (fun x => rVariation r (fun n => g n x)) := by
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact rVariation_congr r _ _ hx

theorem variationChain_le_rVariation (r : ℝ) (a : ℕ → ℂ)
    (J : ℕ) (j : Fin (J + 1) → ℕ) (hj : StrictMono j) :
    variationChain r a J j ≤ rVariation r a := by
  exact (le_iSup_of_le J (le_iSup_of_le j (by simp [hj])))

theorem rVariation_add_le {r : ℝ} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    rVariation r (fun n => a n + b n) ≤ rVariation r a + rVariation r b := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  unfold rVariation
  refine iSup_le fun J => iSup_le fun j => ?_
  split_ifs with hj
  · calc
      variationChain r (fun n => a n + b n) J j ≤
          (∑ h : Fin J, (‖a (j h.succ) - a (j h.castSucc)‖ₑ +
            ‖b (j h.succ) - b (j h.castSucc)‖ₑ) ^ r) ^ (1 / r) := by
        unfold variationChain
        gcongr with h
        have heq : (a (j h.succ) + b (j h.succ)) -
            (a (j h.castSucc) + b (j h.castSucc)) =
            (a (j h.succ) - a (j h.castSucc)) +
            (b (j h.succ) - b (j h.castSucc)) := by ring
        rw [heq]
        exact enorm_add_le _ _
      _ ≤ variationChain r a J j + variationChain r b J j :=
        ENNReal.Lp_add_le Finset.univ _ _ hr
      _ ≤ _ := add_le_add
        (le_iSup_of_le J (le_iSup_of_le j (by simp [hj])))
        (le_iSup_of_le J (le_iSup_of_le j (by simp [hj])))
  · exact zero_le _

/-- The elementary finite-dimensional inequality ℓʳ ≤ ℓ¹, for r≥1. -/
theorem ennreal_rpow_sum_rpow_le_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i ∈ s, f i ^ r) ^ (1 / r) ≤ ∑ i ∈ s, f i := by
  classical
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hi : 0 ≤ 1 / r := by positivity
  have hi1 : 1 / r ≤ 1 := (div_le_one hr0).mpr hr
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr0)]
      exact le_rfl
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      calc
        (f i ^ r + ∑ k ∈ s, f k ^ r) ^ (1 / r) ≤
            (f i ^ r) ^ (1 / r) + (∑ k ∈ s, f k ^ r) ^ (1 / r) :=
          ENNReal.rpow_add_le_add_rpow _ _ hi hi1
        _ ≤ f i + ∑ k ∈ s, f k := by
          simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne',
            ENNReal.rpow_one] using add_le_add_left ih ((f i ^ r) ^ (1 / r))

theorem rVariation_le_two_tsum {r : ℝ} (hr : 1 ≤ r) (a : ℕ → ℂ) :
    rVariation r a ≤ 2 * ∑' n, ‖a n‖ₑ := by
  unfold rVariation
  refine iSup_le fun J => iSup_le fun j => ?_
  split_ifs with hj
  · have hleft : (∑ h : Fin J, ‖a (j h.castSucc)‖ₑ) ≤ ∑' n, ‖a n‖ₑ := by
      simpa only [tsum_fintype] using
        ENNReal.tsum_comp_le_tsum_of_injective
          (hj.injective.comp (Fin.castSucc_injective J)) (fun n => ‖a n‖ₑ)
    have hright : (∑ h : Fin J, ‖a (j h.succ)‖ₑ) ≤ ∑' n, ‖a n‖ₑ := by
      simpa only [tsum_fintype] using
        ENNReal.tsum_comp_le_tsum_of_injective
          (hj.injective.comp (Fin.succ_injective J)) (fun n => ‖a n‖ₑ)
    calc
      variationChain r a J j ≤
          ∑ h : Fin J, ‖a (j h.succ) - a (j h.castSucc)‖ₑ :=
        ennreal_rpow_sum_rpow_le_sum Finset.univ _ hr
      _ ≤ ∑ h : Fin J, (‖a (j h.succ)‖ₑ + ‖a (j h.castSucc)‖ₑ) :=
        Finset.sum_le_sum (fun _ _ => by
          simpa only [enorm_eq_nnnorm, ← ENNReal.coe_add] using
            ENNReal.coe_le_coe.mpr (nnnorm_sub_le _ _))
      _ = (∑ h : Fin J, ‖a (j h.succ)‖ₑ) +
          ∑ h : Fin J, ‖a (j h.castSucc)‖ₑ := Finset.sum_add_distrib
      _ ≤ (∑' n, ‖a n‖ₑ) + ∑' n, ‖a n‖ₑ := add_le_add hright hleft
      _ = 2 * ∑' n, ‖a n‖ₑ := (two_mul _).symm
  · exact zero_le _

theorem variationChain_mul {r : ℝ} (hr : 0 < r) (c : ℂ) (a : ℕ → ℂ)
    (J : ℕ) (j : Fin (J + 1) → ℕ) :
    variationChain r (fun n => c * a n) J j = ‖c‖ₑ * variationChain r a J j := by
  simp only [variationChain, ← mul_sub, enorm_mul,
    ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← Finset.mul_sum,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

theorem rVariation_mul {r : ℝ} (hr : 0 < r) (c : ℂ) (a : ℕ → ℂ) :
    rVariation r (fun n => c * a n) = ‖c‖ₑ * rVariation r a := by
  simp only [rVariation, ENNReal.mul_iSup]
  congr 1
  funext J
  congr 1
  funext j
  split_ifs <;> simp [variationChain_mul hr]

theorem measurable_rVariation {X : Type*} [MeasurableSpace X]
    (r : ℝ) (f : ℕ → X → ℂ) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => rVariation r (fun n => f n x)) := by
  unfold rVariation variationChain
  refine Measurable.iSup fun J => Measurable.iSup fun j => ?_
  split_ifs
  · exact (Finset.measurable_sum _ (fun h _ =>
      ((hf _).sub (hf _)).enorm.pow_const r)).pow_const (1 / r)
  · exact measurable_const

theorem aemeasurable_rVariation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (f : ℕ → X → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) :
    AEMeasurable (fun x => rVariation r (fun n => f n x)) μ := by
  unfold rVariation variationChain
  refine AEMeasurable.iSup fun J => AEMeasurable.iSup fun j => ?_
  split_ifs
  · exact (Finset.aemeasurable_sum _ (fun h _ =>
      ((hf _).sub (hf _)).enorm.pow_const r)).pow_const (1 / r)
  · exact aemeasurable_const

/-- Tonelli converts the pointwise summable-perturbation bound into the
L¹ estimate used by the new corollary. No finiteness premise is needed. -/
theorem lintegral_rVariation_le_two_tsum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {r : ℝ} (hr : 1 ≤ r) (f : ℕ → X → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) :
    (∫⁻ x, rVariation r (fun n => f n x) ∂μ) ≤
      2 * ∑' n, ∫⁻ x, ‖f n x‖ₑ ∂μ := by
  calc
    (∫⁻ x, rVariation r (fun n => f n x) ∂μ) ≤
        ∫⁻ x, 2 * ∑' n, ‖f n x‖ₑ ∂μ :=
      lintegral_mono (fun x => rVariation_le_two_tsum hr _)
    _ = 2 * ∑' n, ∫⁻ x, ‖f n x‖ₑ ∂μ := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_tsum (fun n => (hf n).enorm)]

/-- An infinite summable perturbation changes the L¹ variation by at most
twice the sum of its L¹ sizes. This is the complete abstract transfer step. -/
theorem lintegral_rVariation_le_add_two_tsum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {r : ℝ} (hr : 1 ≤ r) (f g : ℕ → X → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : ∀ n, AEStronglyMeasurable (g n) μ) :
    (∫⁻ x, rVariation r (fun n => f n x) ∂μ) ≤
      (∫⁻ x, rVariation r (fun n => g n x) ∂μ) +
        2 * ∑' n, ∫⁻ x, ‖f n x - g n x‖ₑ ∂μ := by
  calc
    (∫⁻ x, rVariation r (fun n => f n x) ∂μ) ≤
        ∫⁻ x, rVariation r (fun n => g n x) +
          rVariation r (fun n => f n x - g n x) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [add_sub_cancel] using
        rVariation_add_le hr (fun n => g n x) (fun n => f n x - g n x)
    _ = (∫⁻ x, rVariation r (fun n => g n x) ∂μ) +
        ∫⁻ x, rVariation r (fun n => f n x - g n x) ∂μ :=
      lintegral_add_left' (aemeasurable_rVariation μ r g hg) _
    _ ≤ _ := add_le_add_left
      (lintegral_rVariation_le_two_tsum μ hr _ (fun n => (hf n).sub (hg n))) _

end PSPrimes
