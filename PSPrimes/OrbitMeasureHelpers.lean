import PSPrimes.Representatives

/-!
# Measure-theoretic steps in the finite-to-orbit transference argument

All measurability, integrability, and explicit complex duality used here are
proved from the probability-system hypotheses. No analytic estimate is assumed.
-/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory

namespace PSPrimes

theorem orbitProduct_aestronglyMeasurable {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (P : Fin ℓ → Polynomial ℤ)
    (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (n : ℕ) :
    AEStronglyMeasurable (fun x => orbitProduct P T f n x) μ := by
  exact Finset.aestronglyMeasurable_prod Finset.univ fun i _ =>
    (hf i).comp_quasiMeasurePreserving (T.preserving _).quasiMeasurePreserving

/-- Every finite weighted orbit average is integrable, including cutoff zero.
Only an essential bound is imposed on the original representatives. -/
theorem weighted_orbitAverage_integrable {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (P : Fin ℓ → Polynomial ℤ) (T : IntegerAction X μ)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hb : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) (g : ℕ → ℝ) (N : ℕ) :
    Integrable (fun x => weightedAverage g (fun n => orbitProduct P T f n x) N) μ := by
  have hint (n : ℕ) : Integrable (fun x => orbitProduct P T f n x) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (orbitProduct_aestronglyMeasurable P T f hf n)
    filter_upwards [ae_orbitProduct_oneBounded P T f hb] with x hx
    exact hx n
  exact (integrable_finset_sum (initialInterval N)
    (fun n _ => (hint n).const_mul (g n : ℂ))).const_mul (N : ℂ)⁻¹

/-- The explicit multiplier realizes complex L1 duality without a choice of
an unproved dual-space representative. At zero it takes the value zero. -/
def orbitDualMultiplier (z : ℂ) : ℂ := starRingEnd ℂ z / (‖z‖ : ℂ)

theorem norm_orbitDualMultiplier_le (z : ℂ) : ‖orbitDualMultiplier z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [orbitDualMultiplier, hz]
  · have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [orbitDualMultiplier, norm_div, Complex.norm_conj, abs_of_nonneg (norm_nonneg z),
      div_self hnorm]

theorem orbitDualMultiplier_mul (z : ℂ) :
    orbitDualMultiplier z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [orbitDualMultiplier, hz]
  · have hnorm : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    rw [orbitDualMultiplier, div_mul_eq_mul_div, Complex.conj_mul']
    field_simp
    ring

theorem aestronglyMeasurable_orbitDualMultiplier {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {A : X → ℂ}
    (hA : AEStronglyMeasurable A μ) :
    AEStronglyMeasurable (fun x => orbitDualMultiplier (A x)) μ := by
  apply AEMeasurable.aestronglyMeasurable
  exact (Complex.continuous_conj.measurable.comp_aemeasurable hA.aemeasurable).div
    (Complex.measurable_ofReal.comp_aemeasurable hA.norm.aemeasurable)

theorem orbitDualPair_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {A : X → ℂ} (hA : Integrable A μ) :
    Integrable (fun x => orbitDualMultiplier (A x) * A x) μ := by
  simpa only [orbitDualMultiplier_mul] using hA.norm.ofReal

theorem integral_orbitDualPair {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (A : X → ℂ) :
    (∫ x, orbitDualMultiplier (A x) * A x ∂μ) =
      ((∫ x, ‖A x‖ ∂μ : ℝ) : ℂ) := by
  simp only [orbitDualMultiplier_mul, integral_complex_ofReal]

/-- Change of variables under an integer action, with almost-everywhere
strong measurability rather than an additional embedding hypothesis. -/
theorem integerAction_integral_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (T : IntegerAction X μ) (a : ℤ) (F : X → ℂ)
    (hF : AEStronglyMeasurable F μ) :
    (∫ x, F (T.act a x) ∂μ) = ∫ x, F x ∂μ := by
  have hFm : AEStronglyMeasurable F (Measure.map (T.act a) μ) := by
    simpa only [(T.preserving a).map_eq] using hF
  have h := integral_map (T.preserving a).measurable.aemeasurable hFm
  simpa only [(T.preserving a).map_eq] using h.symm

end PSPrimes
