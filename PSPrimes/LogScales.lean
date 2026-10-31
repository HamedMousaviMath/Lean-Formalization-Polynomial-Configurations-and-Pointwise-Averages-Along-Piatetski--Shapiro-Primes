import PSPrimes.AsymptoticScales

/-!
# Logarithmic length estimates from the actual finite increment

The coefficient and exponents in the progression-length lower bound remain
explicit. All resulting constants are chosen before the stage variables.
-/

noncomputable section

namespace PSPrimes

/-- Taking logarithms of the exact floor scale loses at most `log 2`. -/
theorem log_floorScale_lower (N Q d : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hd : 1 ≤ d) (hM : 1 ≤ floorScale N Q d) :
    (Real.log N - ((d : ℝ) - 1) * Real.log Q) / (d : ℝ) - Real.log 2 ≤
      Real.log (floorScale N Q d : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hMr : (0 : ℝ) < floorScale N Q d := by exact_mod_cast hM
  have hroot : 0 < rootScale N Q d := by
    unfold rootScale
    exact Real.rpow_pos_of_pos (div_pos hNr (pow_pos hQr _)) _
  have hlog := Real.log_le_log hroot (rootScale_lt_twice_floor N Q d hM).le
  have hrootlog : Real.log (rootScale N Q d) =
      (Real.log N - ((d : ℝ) - 1) * Real.log Q) / (d : ℝ) := by
    unfold rootScale
    rw [Real.log_rpow (div_pos hNr (pow_pos hQr _)),
      Real.log_div hNr.ne' (pow_ne_zero _ hQr.ne'), Real.log_pow,
      Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [hrootlog, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hMr.ne'] at hlog
  linarith

/-- The floor scale never exceeds the ambient length, hence neither does
its logarithm. -/
theorem log_floorScale_le_log_length (N Q d : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hd : 1 ≤ d) (hM : 1 ≤ floorScale N Q d) :
    Real.log (floorScale N Q d : ℝ) ≤ Real.log N := by
  apply Real.log_le_log (by exact_mod_cast hM)
  exact_mod_cast floorScale_le_length N Q d hN hQ hd

/-- The exact logarithm of the finite length lower bound. In particular the
positive multiplicative constant is not silently replaced by one. -/
theorem log_increment_length_exact (N Q d r Aq Aδ N' : ℕ)
    (hQ : 1 ≤ Q) (hM : 1 ≤ floorScale N Q d)
    (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c)
    (hlength : c * (Q : ℝ)^(-(Aq : ℝ)) * δ^Aδ *
      (floorScale N Q d : ℝ)^r *
      Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ))) ≤ (N' : ℝ)) :
    Real.log c - (Aq : ℝ) * Real.log Q + (Aδ : ℝ) * Real.log δ +
      (r : ℝ) * Real.log (floorScale N Q d : ℝ) -
      (d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ)) ≤ Real.log N' := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hMr : (0 : ℝ) < floorScale N Q d := by exact_mod_cast hM
  have hprod : 0 < c * (Q : ℝ)^(-(Aq : ℝ)) * δ^Aδ *
      (floorScale N Q d : ℝ)^r *
      Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ))) := by
    positivity
  have hlog := Real.log_le_log hprod hlength
  have heq : Real.log (c * (Q : ℝ)^(-(Aq : ℝ)) * δ^Aδ *
      (floorScale N Q d : ℝ)^r *
      Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ)))) =
      Real.log c - (Aq : ℝ) * Real.log Q + (Aδ : ℝ) * Real.log δ +
        (r : ℝ) * Real.log (floorScale N Q d : ℝ) -
        (d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ)) := by
    repeat' rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_rpow hQr, Real.log_pow, Real.log_pow, Real.log_exp]
    ring
  rwa [heq] at hlog

/-- Uniform logarithmic recursion derived from the genuine finite lower bound.
The constant depends only on the fixed degree data, exponents and positive
prefactor; it is chosen before every stage length, modulus and density. -/
theorem log_increment_length_lower_bound (d r Aq Aδ : ℕ)
    (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q N' : ℕ,
      1 ≤ N → 1 ≤ Q → 1 ≤ floorScale N Q d → 1 ≤ Real.log N →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        c * (Q : ℝ)^(-(Aq : ℝ)) * δ^Aδ *
          (floorScale N Q d : ℝ)^r *
          Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ))) ≤ (N' : ℝ) →
        (r : ℝ) / (d : ℝ) * Real.log N -
          C * (Real.log Q + Real.log δ⁻¹ + Real.sqrt (Real.log N)) ≤ Real.log N' := by
  let B : ℝ := |Real.log c| + (r : ℝ) * Real.log 2
  let C : ℝ := 1 + ((Aq : ℝ) + d) + Aδ + d + B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N Q N' hN hQ hM hlogN δ hδ hδ₁ hlength
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hrr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hrdr : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hθ : (r : ℝ) / d ≤ 1 := (div_le_one hdr).mpr hrdr
  have hq : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  have ha : 0 ≤ Real.log δ⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hδ.le hδ₁)
  have hs : 1 ≤ Real.sqrt (Real.log N) := Real.one_le_sqrt.mpr hlogN
  have hlogM := log_floorScale_lower N Q d hN hQ hd hM
  have hlogMU := log_floorScale_le_log_length N Q d hN hQ hd hM
  have hsqrt := Real.sqrt_le_sqrt hlogMU
  have hlogLength := log_increment_length_exact N Q d r Aq Aδ N' hQ hM δ c hδ hc hlength
  have hlogc : -|Real.log c| ≤ Real.log c := neg_abs_le _
  have hlogtwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hqcoeff : (r : ℝ) / d * ((d : ℝ) - 1) ≤ d := by
    have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hlogMmul := mul_le_mul_of_nonneg_left hlogM hrr
  have hlogMmul' : (r : ℝ) / (d : ℝ) * Real.log N -
      ((r : ℝ) / d * ((d : ℝ) - 1)) * Real.log Q - (r : ℝ) * Real.log 2 ≤
        (r : ℝ) * Real.log (floorScale N Q d : ℝ) := by
    convert hlogMmul using 1 <;> ring
  have hqLoss := mul_le_mul_of_nonneg_right hqcoeff hq
  have hsLoss := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg d)
  have hBabsorb := mul_le_mul_of_nonneg_left hs hB
  have hAqr : (0 : ℝ) ≤ Aq := Nat.cast_nonneg Aq
  have hAδr : (0 : ℝ) ≤ Aδ := Nat.cast_nonneg Aδ
  have hCq : (Aq : ℝ) + d ≤ C := by dsimp [C]; linarith
  have hCa : (Aδ : ℝ) ≤ C := by dsimp [C]; linarith
  have hCs : (d : ℝ) + B ≤ C := by dsimp [C]; linarith
  have heqQ := mul_le_mul_of_nonneg_right hCq hq
  have heqA := mul_le_mul_of_nonneg_right hCa ha
  have heqS := mul_le_mul_of_nonneg_right hCs (Real.sqrt_nonneg (Real.log N))
  rw [Real.log_inv] at ha heqA ⊢
  dsimp [B] at hBabsorb heqS
  linear_combination hlogLength + hlogMmul' + hqLoss + hsLoss + hlogc + hBabsorb + heqQ + heqA + heqS

/-- The same constant works at every increasing-density stage: the logarithmic
error is bounded using the initial density `α`, with no stage dependence. -/
theorem log_increment_length_lower_bound_initial_density (d r Aq Aδ : ℕ)
    (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q N' : ℕ,
      1 ≤ N → 1 ≤ Q → 1 ≤ floorScale N Q d → 1 ≤ Real.log N →
      ∀ α δ : ℝ, 0 < α → α ≤ δ → δ ≤ 1 →
        c * (Q : ℝ)^(-(Aq : ℝ)) * δ^Aδ *
          (floorScale N Q d : ℝ)^r *
          Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ))) ≤ (N' : ℝ) →
        (r : ℝ) / (d : ℝ) * Real.log N -
          C * (Real.log Q + Real.log α⁻¹ + Real.sqrt (Real.log N)) ≤ Real.log N' := by
  obtain ⟨C, hC, hlength⟩ := log_increment_length_lower_bound d r Aq Aδ hd hr hrd c hc
  refine ⟨C, hC, ?_⟩
  intro N Q N' hN hQ hM hlogN α δ hα hαδ hδ₁ hfinite
  have hδ : 0 < δ := hα.trans_le hαδ
  have hlog := Real.log_le_log hα hαδ
  have hlogInv : Real.log δ⁻¹ ≤ Real.log α⁻¹ := by
    simp only [Real.log_inv]
    linarith
  have herr : C * (Real.log Q + Real.log δ⁻¹ + Real.sqrt (Real.log N)) ≤
      C * (Real.log Q + Real.log α⁻¹ + Real.sqrt (Real.log N)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC.le
  exact (sub_le_sub_left herr _).trans
    (hlength N Q N' hN hQ hM hlogN δ hδ hδ₁ hfinite)

end PSPrimes
