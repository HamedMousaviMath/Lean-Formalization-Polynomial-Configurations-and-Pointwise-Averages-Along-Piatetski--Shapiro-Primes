import PSPrimes.ExceptionalTerms

/-!
# Elementary removal of higher prime powers

The finite set consists of distinct integers, not a list with multiplicities.
All estimates here are proved from elementary Mathlib arithmetic results.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- The higher prime powers p^k≤N, k≥2, as a finite set of integers. -/
def higherPrimePowers (N : ℕ) : Finset ℕ :=
  (initialInterval N).filter (fun n => IsPrimePow n ∧ ¬n.Prime)

/-- Every nonprime prime power below N has a small base and logarithmic exponent. -/
theorem higherPrimePower_representation {N n : ℕ} (hn : n ∈ higherPrimePowers N) :
    ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ≤ Nat.sqrt N ∧ k ≤ Nat.log 2 N ∧ p ^ k = n := by
  obtain ⟨hnI, hpow, hnot⟩ := Finset.mem_filter.mp hn
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpow
  have hnN : n ≤ N := (Finset.mem_Icc.mp hnI).2
  have hk₂ : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    subst k
    simp only [pow_one] at hpk
    exact hnot (hpk ▸ hp)
  have hpN : p ^ k ≤ N := hpk ▸ hnN
  refine ⟨p, k, hp, hk₂, ?_, ?_, hpk⟩
  · exact Nat.le_sqrt'.mpr ((pow_le_pow_right₀ hp.one_lt.le hk₂).trans hpN)
  · exact Nat.le_log_of_pow_le (by norm_num)
      ((Nat.pow_le_pow_left hp.two_le k).trans hpN)

/-- A direct rectangular cover gives at most sqrt(N)*log_2(N) higher prime powers. -/
theorem card_higherPrimePowers_le (N : ℕ) :
    (higherPrimePowers N).card ≤ Nat.sqrt N * Nat.log 2 N := by
  classical
  let candidates : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 (Nat.sqrt N)).product (Finset.Icc 1 (Nat.log 2 N))
  have hsub : higherPrimePowers N ⊆ candidates.image (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    obtain ⟨p, k, hp, hk, hpN, hkN, hpk⟩ := higherPrimePower_representation hn
    apply Finset.mem_image.mpr
    refine ⟨(p, k), ?_, hpk⟩
    change (p, k) ∈ (Finset.Icc 1 (Nat.sqrt N)).product (Finset.Icc 1 (Nat.log 2 N))
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hpN⟩,
      Finset.mem_Icc.mpr ⟨by omega, hkN⟩⟩
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_image_le.trans
  simp [candidates, Nat.card_Icc]

/-- The ordinary von Mangoldt mass of higher prime powers. -/
theorem higherPrimePowers_mangoldt_mass_le (N : ℕ) :
    (∑ n ∈ higherPrimePowers N, ArithmeticFunction.vonMangoldt n) ≤
      (Nat.sqrt N * Nat.log 2 N : ℕ) * Real.log N := by
  calc
    (∑ n ∈ higherPrimePowers N, ArithmeticFunction.vonMangoldt n) ≤
        ∑ _n ∈ higherPrimePowers N, Real.log N := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hI, _⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn₁, hnN⟩ := Finset.mem_Icc.mp hI
      apply ArithmeticFunction.vonMangoldt_le_log.trans
      apply Real.log_le_log
      · exact_mod_cast hn₁
      · exact_mod_cast hnN
    _ = ((higherPrimePowers N).card : ℝ) * Real.log N := by simp
    _ ≤ (Nat.sqrt N * Nat.log 2 N : ℕ) * Real.log N :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_higherPrimePowers_le N)
        (Real.log_natCast_nonneg N)

/-- A combined pointwise envelope for sparse and ordinary prime weights. -/
theorem sparse_add_mangoldt_le_envelope {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n ≤
      (γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hn.trans hnN
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : ArithmeticFunction.vonMangoldt n ≤ Real.log N :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hn₀ (by exact_mod_cast hnN))
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (1 - γ) :=
    Real.one_le_rpow hN (by linarith)
  calc
    sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n ≤
        γ⁻¹ * (N : ℝ) ^ (1 - γ) * Real.log N +
        (N : ℝ) ^ (1 - γ) * Real.log N := by
      apply add_le_add (sparseMangoldt_le_envelope hγ₀ hγ₁ hn hnN)
      exact hlog.trans (by nlinarith [Real.log_natCast_nonneg N])
    _ = (γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N := by ring

/-- Both weight masses over higher prime powers are controlled by the same elementary cover. -/
theorem higherPrimePowers_combined_mass_le {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (N : ℕ) :
    (∑ n ∈ higherPrimePowers N, (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n)) ≤
      (Nat.sqrt N * Nat.log 2 N : ℕ) *
        ((γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N) := by
  calc
    _ ≤ ∑ _n ∈ higherPrimePowers N,
        (γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N := by
      apply Finset.sum_le_sum
      intro n hn
      have hI := (Finset.mem_filter.mp hn).1
      exact sparse_add_mangoldt_le_envelope hγ₀ hγ₁
        (Finset.mem_Icc.mp hI).1 (Finset.mem_Icc.mp hI).2
    _ = ((higherPrimePowers N).card : ℝ) *
        ((γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_higherPrimePowers_le N)
      (by positivity)

/-- The manuscript's elementary higher-prime-power estimate, with an explicit constant. -/
theorem higherPrimePowers_combined_mass_rpow_le {γ : ℝ}
    (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (N : ℕ) :
    (∑ n ∈ higherPrimePowers N, (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n)) ≤
      ((γ⁻¹ + 1) / Real.log 2) * (N : ℝ) ^ (3 / 2 - γ) * (Real.log N) ^ 2 := by
  by_cases hN : N = 0
  · simp [hN, higherPrimePowers, initialInterval]
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hsqrt : (Nat.sqrt N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt (Nat.cast_nonneg _) hN₀.le).mpr
    exact_mod_cast Nat.sqrt_le' N
  have hlog : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb N 2
  have hB : 0 ≤ (γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N := by positivity
  have hmass := higherPrimePowers_combined_mass_le hγ₀ hγ₁ N
  simp only [Nat.cast_mul] at hmass
  apply hmass.trans
  calc
    (Nat.sqrt N : ℝ) * Nat.log 2 N *
        ((γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) * (Real.log N / Real.log 2) *
        ((γ⁻¹ + 1) * (N : ℝ) ^ (1 - γ) * Real.log N) := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact mul_le_mul hsqrt hlog (Nat.cast_nonneg _) (Real.rpow_nonneg hN₀.le _)
    _ = ((γ⁻¹ + 1) / Real.log 2) *
        ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 - γ)) * (Real.log N) ^ 2 := by ring
    _ = ((γ⁻¹ + 1) / Real.log 2) * (N : ℝ) ^ (3 / 2 - γ) * (Real.log N) ^ 2 := by
      rw [← Real.rpow_add hN₀]
      congr 2
      ring_nf

/-- Higher prime powers have total combined mass o(N) when γ>1/2. -/
theorem higherPrimePowers_combined_mass_div_tendsto_zero {γ : ℝ}
    (hγ₀ : (1 / 2 : ℝ) < γ) (hγ₁ : γ ≤ 1) :
    Filter.Tendsto (fun N : ℕ =>
      (∑ n ∈ higherPrimePowers N, (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n)) /
        (N : ℝ)) Filter.atTop (nhds 0) := by
  have hg : 0 < γ := by linarith
  have hs : 0 < γ - 1 / 2 := by linarith
  have hlimit : Filter.Tendsto (fun N : ℕ =>
      (Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ (γ - 1 / 2)) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hs).tendsto_div_nhds_zero
    simpa only [Function.comp_apply, Real.rpow_two] using
      h.comp (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) _ _)
  have hClimit := hlimit.const_mul ((γ⁻¹ + 1) / Real.log 2)
  simp only [mul_zero] at hClimit
  apply squeeze_zero' ?_ ?_ hClimit
  · apply Filter.Eventually.of_forall
    intro N
    apply div_nonneg
    · exact Finset.sum_nonneg (fun n _ => add_nonneg
        (sparseMangoldt_nonneg hg n) ArithmeticFunction.vonMangoldt_nonneg)
    · exact Nat.cast_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hx : (0 : ℝ) < N := by exact_mod_cast hN
    have hp : (N : ℝ) ^ (3 / 2 - γ) * (N : ℝ) ^ (γ - 1 / 2) = N := by
      rw [← Real.rpow_add hx]
      convert Real.rpow_one (N : ℝ) using 1
      congr 1
      ring
    calc
      _ ≤ (((γ⁻¹ + 1) / Real.log 2) * (N : ℝ) ^ (3 / 2 - γ) * (Real.log N) ^ 2) /
          (N : ℝ) :=
        div_le_div_of_nonneg_right (higherPrimePowers_combined_mass_rpow_le hg hγ₁ N) hx.le
      _ = ((γ⁻¹ + 1) / Real.log 2) *
          ((Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ (γ - 1 / 2)) := by
        rw [← mul_div_assoc]
        apply (div_eq_div_iff hx.ne' (Real.rpow_pos_of_pos hx (γ - 1 / 2)).ne').mpr
        calc
          _ = ((γ⁻¹ + 1) / Real.log 2) * (Real.log N) ^ 2 *
              ((N : ℝ) ^ (3 / 2 - γ) * (N : ℝ) ^ (γ - 1 / 2)) := by ring
          _ = _ := by rw [hp]

end PSPrimes
