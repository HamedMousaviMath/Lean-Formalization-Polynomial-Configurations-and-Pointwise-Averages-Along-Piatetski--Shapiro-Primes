import PSPrimes.PrimeMassInputs

/-!
# Literal normalization of the density-increment length bound

The source parameters can be strengthened by increasing `K₁`. The resulting
admissible range is a subset of the original one, so existing discrepancy
and prime-mass witnesses restrict to it without new external input. The
increased lower bound on the modulus absorbs a fixed positive length
prefactor by increasing the modulus exponent by exactly one.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- Increase only the initialization constant, retaining all source-compatible
comparison, smoothness, and discrepancy constants. -/
def normalizeKMTTParameters {ℓ Adiv : ℕ}
    (p : KMTTComparisonParameters ℓ Adiv) (cLength : ℝ) :
    KMTTComparisonParameters ℓ Adiv :=
  { p with
    K₁ := max p.K₁ cLength⁻¹
    K₁_ge := p.K₁_ge.trans (le_max_left _ _)
    divisibility_constant := p.divisibility_constant.trans (le_max_left _ _) }

/-- The logarithmic density lower bound always implies genuine positivity,
including the finite edge cases `N=0` and `N=1`. -/
theorem KMTTAdmissible.density_pos {ℓ Adiv N Q s : ℕ}
    {p : KMTTComparisonParameters ℓ Adiv} {δ : ℝ}
    (h : KMTTAdmissible p N Q s δ) : 0 < δ :=
  lt_of_le_of_lt (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) h.2.2.1

/-- Increasing `K₁` restricts admissibility; it strengthens no external theorem. -/
theorem KMTTAdmissible.of_normalized {ℓ Adiv N Q s : ℕ}
    {p : KMTTComparisonParameters ℓ Adiv} {cLength δ : ℝ}
    (h : KMTTAdmissible (normalizeKMTTParameters p cLength) N Q s δ) :
    KMTTAdmissible p N Q s δ := by
  obtain ⟨hQ, hs, hδlo, hδhi, hceil, hS, hQrange, hsmooth, hlcm⟩ := h
  have hδ : 0 < δ :=
    lt_of_le_of_lt (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) hδlo
  refine ⟨hQ, hs, hδlo, hδhi, ?_, hS, hQrange, hsmooth, hlcm⟩
  have hmul : p.K₁ * δ ^ (-p.C₁) ≤
      (normalizeKMTTParameters p cLength).K₁ * δ ^ (-p.C₁) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ.le _)
  exact (Nat.ceil_mono hmul).trans hceil

/-- The exact same discrepancy theorem and threshold apply after restricting
the admissible range to the normalized parameters. -/
theorem KMTTUnweightedWitness.normalize {C cLength : ℝ} {d ℓ Adiv : ℕ}
    {p : KMTTComparisonParameters ℓ Adiv}
    (h : KMTTUnweightedWitness C d ℓ Adiv p) :
    KMTTUnweightedWitness C d ℓ Adiv (normalizeKMTTParameters p cLength) := by
  obtain ⟨Nmin, hw⟩ := h
  refine ⟨Nmin, ?_⟩
  intro N hN Q s δ hAd
  exact hw N hN Q s δ hAd.of_normalized

/-- Restrict an existing compatible prime-mass witness. Its cutoff, lower
constant, exponent constant, and threshold are all unchanged definitionally. -/
def PrimeProgressionMassWitness.normalize {ℓ Adiv d : ℕ} {τmax : ℝ}
    {p : KMTTComparisonParameters ℓ Adiv}
    (w : PrimeProgressionMassWitness p d τmax) (cLength : ℝ) :
    PrimeProgressionMassWitness (normalizeKMTTParameters p cLength) d τmax where
  cutoff := w.cutoff
  cutoff_pos := w.cutoff_pos
  cutoff_le_one := w.cutoff_le_one
  cutoff_le := w.cutoff_le
  lowerConstant := w.lowerConstant
  lowerConstant_pos := w.lowerConstant_pos
  exponentConstant := w.exponentConstant
  exponentConstant_pos := w.exponentConstant_pos
  threshold := w.threshold
  truncated_mass := by
    intro N Q s δ hN hAd
    exact w.truncated_mass N Q s δ hN hAd.of_normalized
  full_mass := by
    intro N Q s δ hN hAd
    exact w.full_mass N Q s δ hN hAd.of_normalized

/-- The initialization and lcm-divisibility conditions force the normalized
modulus to be at least the inverse length prefactor. -/
theorem normalized_admissible_modulus_lower {ℓ Adiv N Q s : ℕ}
    {p : KMTTComparisonParameters ℓ Adiv} {cLength δ : ℝ}
    (_hc : 0 < cLength)
    (h : KMTTAdmissible (normalizeKMTTParameters p cLength) N Q s δ) :
    cLength⁻¹ ≤ (Q : ℝ) := by
  have hδ := h.density_pos
  obtain ⟨hQ, hs, hδlo, hδhi, hceil, hS, hQrange, hsmooth, hlcm⟩ := h
  have hpow : (1 : ℝ) ≤ δ ^ (-p.C₁) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδhi (by linarith [p.C₁_ge])
  have hKpos : 0 ≤ (normalizeKMTTParameters p cLength).K₁ :=
    le_trans (by norm_num) (normalizeKMTTParameters p cLength).K₁_ge
  have hKmul : (normalizeKMTTParameters p cLength).K₁ ≤
      (normalizeKMTTParameters p cLength).K₁ * δ ^ (-p.C₁) := by
    simpa using mul_le_mul_of_nonneg_left hpow hKpos
  have hsQ : s ≤ Q :=
    (Nat.le_of_dvd (smoothModulus_pos s) (dvd_smoothModulus (by omega) le_rfl)).trans
      (Nat.le_of_dvd (by omega : 0 < Q) hlcm)
  calc
    cLength⁻¹ ≤ (normalizeKMTTParameters p cLength).K₁ := le_max_right _ _
    _ ≤ (normalizeKMTTParameters p cLength).K₁ * δ ^ (-p.C₁) := hKmul
    _ ≤ (⌈(normalizeKMTTParameters p cLength).K₁ * δ ^ (-p.C₁)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (s : ℝ) := by exact_mod_cast hceil
    _ ≤ (Q : ℝ) := by exact_mod_cast hsQ

/-- A fixed positive prefactor is absorbed by one extra inverse modulus
power. The modulus exponent is increased by one, independently of `C`. -/
theorem length_prefactor_absorb {q cLength : ℝ} (hq : 0 < q) (hc : 0 < cLength)
    (hlarge : cLength⁻¹ ≤ q) (A : ℕ) :
    q ^ (-((A + 1 : ℕ) : ℝ)) ≤ cLength * q ^ (-(A : ℝ)) := by
  have hinv : q⁻¹ ≤ cLength := by
    simpa using (inv_le_inv₀ hq (inv_pos.mpr hc)).mpr hlarge
  have hexp : -((A + 1 : ℕ) : ℝ) = -(A : ℝ) + (-1 : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_add hq, Real.rpow_neg_one]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hq.le (-(A : ℝ)))

/-- Direct form for the normalized source parameters. -/
theorem normalized_length_prefactor_absorb {ℓ Adiv N Q s : ℕ}
    {p : KMTTComparisonParameters ℓ Adiv} {cLength δ : ℝ}
    (hc : 0 < cLength)
    (h : KMTTAdmissible (normalizeKMTTParameters p cLength) N Q s δ) (A : ℕ) :
    (Q : ℝ) ^ (-((A + 1 : ℕ) : ℝ)) ≤ cLength * (Q : ℝ) ^ (-(A : ℝ)) :=
  length_prefactor_absorb (by exact_mod_cast (by have := h.1; omega : 0 < Q)) hc
    (normalized_admissible_modulus_lower hc h) A

/-- Multiplying by the remaining nonnegative length factors preserves the
literal source normalization; no sign assumption is hidden in the use. -/
theorem normalized_length_prefactor_absorb_mul {ℓ Adiv N Q s : ℕ}
    {p : KMTTComparisonParameters ℓ Adiv} {cLength δ F : ℝ}
    (hc : 0 < cLength)
    (h : KMTTAdmissible (normalizeKMTTParameters p cLength) N Q s δ)
    (A : ℕ) (hF : 0 ≤ F) :
    (Q : ℝ) ^ (-((A + 1 : ℕ) : ℝ)) * F ≤
      cLength * (Q : ℝ) ^ (-(A : ℝ)) * F :=
  mul_le_mul_of_nonneg_right (normalized_length_prefactor_absorb hc h A) hF

end PSPrimes
