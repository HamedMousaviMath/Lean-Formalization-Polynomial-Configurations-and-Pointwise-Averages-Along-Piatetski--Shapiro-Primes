import PSPrimes.DensityIncrement
import PSPrimes.KMTTNormalization

noncomputable section
namespace PSPrimes

/-- The explicit positive resolution prefactor is removed by a proved
permitted K₁ enlargement and one additional inverse modulus power. -/
theorem KMTTDensityIncrementWitness.normalize_length
    {C c₂ cLength : ℝ} {d ℓ Adiv Bmax Aq Aδ : ℕ}
    {p : KMTTComparisonParameters ℓ Adiv} (hc : 0 < cLength)
    (h : KMTTDensityIncrementWitness C d ℓ Adiv Bmax Aq Aδ p c₂ cLength) :
    KMTTDensityIncrementWitness C d ℓ Adiv Bmax (Aq + 1) Aδ
      (normalizeKMTTParameters p cLength) c₂ 1 := by
  obtain ⟨Nmin, h⟩ := h
  refine ⟨Nmin, ?_⟩
  intro N hN Q s δ had R hcoef hdeg htop A hA hcard hdisc
  obtain ⟨b, hb, hB, a, N', hN', hAP, hgrowth, hlength⟩ :=
    h N hN Q s δ had.of_normalized R hcoef hdeg htop A hA hcard hdisc
  refine ⟨b, hb, hB, a, N', hN', hAP, hgrowth, ?_⟩
  let F : ℝ := δ ^ Aδ * (floorScale N Q d : ℝ) ^ firstDegree R *
    Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ)))
  have hF : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg had.density_pos.le _) (by positivity))
      (Real.exp_pos _).le
  calc
    1 * (Q : ℝ) ^ (-((Aq + 1 : ℕ) : ℝ)) * δ ^ Aδ *
        (floorScale N Q d : ℝ) ^ firstDegree R *
        Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ))) =
        (Q : ℝ) ^ (-((Aq + 1 : ℕ) : ℝ)) * F := by dsimp [F]; ring
    _ ≤ cLength * (Q : ℝ) ^ (-(Aq : ℝ)) * F :=
      normalized_length_prefactor_absorb_mul hc had Aq hF
    _ = cLength * (Q : ℝ) ^ (-(Aq : ℝ)) * δ ^ Aδ *
        (floorScale N Q d : ℝ) ^ firstDegree R *
        Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ))) := by dsimp [F]; ring
    _ ≤ N' := hlength

/-- Literal Proposition 3.1 normalization: the length bound has coefficient
one; all source dependencies and the degree-only exponents are retained. -/
theorem kmtt_density_increment_normalized
    (hUW : KMTTUnweightedInput) (hReg : KMTTRegularityInput) :
    ∀ d : ℕ, 1 ≤ d → ∃ Bmax : ℕ, 1 ≤ Bmax ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ Aq Aδ : ℕ, 1 ≤ Aq ∧ 1 ≤ Aδ ∧
        ∀ C : ℝ, 1 ≤ C → ∃ Adiv : ℕ,
          ∃ p : KMTTComparisonParameters ℓ Adiv,
          ∃ c₂ : ℝ, 0 < c₂ ∧
            KMTTDensityIncrementWitness C d ℓ Adiv Bmax Aq Aδ p c₂ 1 := by
  intro d hd
  obtain ⟨Bmax, hB, hD⟩ := kmtt_density_increment hUW hReg d hd
  refine ⟨Bmax, hB, ?_⟩
  intro ℓ hℓ
  obtain ⟨Aq, Aδ, hAq, hAδ, hL⟩ := hD ℓ hℓ
  refine ⟨Aq + 1, Aδ, by omega, hAδ, ?_⟩
  intro C hC
  obtain ⟨Adiv, p, c₂, hc₂, cLength, hc, h⟩ := hL C hC
  exact ⟨Adiv, normalizeKMTTParameters p cLength, c₂, hc₂,
    KMTTDensityIncrementWitness.normalize_length hc h⟩

end PSPrimes
