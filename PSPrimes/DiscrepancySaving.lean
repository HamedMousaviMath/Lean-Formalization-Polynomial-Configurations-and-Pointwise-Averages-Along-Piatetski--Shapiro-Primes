import PSPrimes.PrimeDiscrepancy
import PSPrimes.SmallScale

/-!
# Uniform saving for the actual collision and prime-power errors

The explicit error is the error in `PrimeDiscrepancy.lean`, with its actual
integer cutoffs and both elementary contributions. No discrepancy conclusion
or density-increment assertion is added as a hypothesis.
-/

noncomputable section
open Filter Topology

namespace PSPrimes

/-- An explicit constant before transferring the lifted scale back to `N`. -/
def sparseErrorLiftConstant (γ : ℝ) (d ℓ : ℕ) : ℝ :=
  (2 : ℝ) ^ (13 / 16 : ℝ) *
    (32 * (d * (ℓ + 1).choose 2 : ℕ) * γ⁻¹ +
      1024 * ((γ⁻¹ + 1) / Real.log 2))

theorem sparseErrorLiftConstant_pos {γ : ℝ} (hγ : 0 < γ) (d ℓ : ℕ) :
    0 < sparseErrorLiftConstant γ d ℓ := by
  unfold sparseErrorLiftConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- Both logarithmic contributions admit one common elementary envelope. -/
theorem sparse_error_numerator_le {γ L : ℝ} (hγ : 0 < γ)
    (hγlower : 3 / 4 ≤ γ) (hL : 1 ≤ L) (d ℓ : ℕ) :
    (d * (ℓ + 1).choose 2 : ℕ) *
        (γ⁻¹ * (L + 1) ^ (1 - γ) * Real.log (L + 1)) +
      ((γ⁻¹ + 1) / Real.log 2) * (L + 1) ^ (3 / 2 - γ) *
        (Real.log (L + 1)) ^ 2 ≤
      sparseErrorLiftConstant γ d ℓ * L ^ (13 / 16 : ℝ) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hX : 1 ≤ L + 1 := by linarith
  have hXpos : 0 < L + 1 := by linarith
  have hlog : 0 ≤ Real.log (L + 1) := Real.log_nonneg hX
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogbound : Real.log (L + 1) ≤ 32 * (L + 1) ^ (1 / 32 : ℝ) := by
    have h := Real.log_le_rpow_div hXpos.le (by norm_num : (0 : ℝ) < 1 / 32)
    nlinarith
  have hlogbound' : Real.log (L + 1) ≤ 32 * (L + 1) ^ (1 / 16 : ℝ) := by
    exact hlogbound.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1 / 32 : ℝ) ≤ 1 / 16))
      (by norm_num))
  have hlogsq : (Real.log (L + 1)) ^ 2 ≤ 1024 * (L + 1) ^ (1 / 16 : ℝ) := by
    calc
      _ ≤ (32 * (L + 1) ^ (1 / 32 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlog hlogbound 2
      _ = 1024 * (L + 1) ^ (1 / 16 : ℝ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hXpos.le]
        norm_num
  have hp1 : (L + 1) ^ (1 - γ) ≤ (L + 1) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hp2 : (L + 1) ^ (3 / 2 - γ) ≤ (L + 1) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hcombine : (L + 1) ^ (3 / 4 : ℝ) * (L + 1) ^ (1 / 16 : ℝ) =
      (L + 1) ^ (13 / 16 : ℝ) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hfirst : γ⁻¹ * (L + 1) ^ (1 - γ) * Real.log (L + 1) ≤
      32 * γ⁻¹ * (L + 1) ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ γ⁻¹ * (L + 1) ^ (3 / 4 : ℝ) *
          (32 * (L + 1) ^ (1 / 16 : ℝ)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hp1 (by positivity))
          hlogbound' hlog (by positivity)
      _ = _ := by rw [← hcombine]; ring
  have hsecond : (L + 1) ^ (3 / 2 - γ) * (Real.log (L + 1)) ^ 2 ≤
      1024 * (L + 1) ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ (L + 1) ^ (3 / 4 : ℝ) *
          (1024 * (L + 1) ^ (1 / 16 : ℝ)) :=
        mul_le_mul hp2 hlogsq (sq_nonneg _) (by positivity)
      _ = _ := by rw [mul_left_comm, hcombine]
  have hshift : (L + 1) ^ (13 / 16 : ℝ) ≤
      (2 : ℝ) ^ (13 / 16 : ℝ) * L ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ (2 * L) ^ (13 / 16 : ℝ) :=
        Real.rpow_le_rpow hXpos.le (by linarith) (by norm_num)
      _ = _ := Real.mul_rpow (by norm_num) hLpos.le
  have hcoef : 0 ≤ 32 * (d * (ℓ + 1).choose 2 : ℕ) * γ⁻¹ +
      1024 * ((γ⁻¹ + 1) / Real.log 2) := by positivity
  calc
    _ ≤ (d * (ℓ + 1).choose 2 : ℕ) *
        (32 * γ⁻¹ * (L + 1) ^ (13 / 16 : ℝ)) +
        ((γ⁻¹ + 1) / Real.log 2) *
          (1024 * (L + 1) ^ (13 / 16 : ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg _))
        (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsecond
            (show 0 ≤ (γ⁻¹ + 1) / Real.log 2 by positivity))
    _ = (32 * (d * (ℓ + 1).choose 2 : ℕ) * γ⁻¹ +
        1024 * ((γ⁻¹ + 1) / Real.log 2)) * (L + 1) ^ (13 / 16 : ℝ) := by ring
    _ ≤ (32 * (d * (ℓ + 1).choose 2 : ℕ) * γ⁻¹ +
        1024 * ((γ⁻¹ + 1) / Real.log 2)) *
          ((2 : ℝ) ^ (13 / 16 : ℝ) * L ^ (13 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left hshift hcoef
    _ = _ := by unfold sparseErrorLiftConstant; ring

/-- Finite saving at the lifted scale; the modulus loss is displayed. -/
theorem sparseCountError_le_lifted_power {γ : ℝ} (hγ : 0 < γ)
    (hγlower : 3 / 4 ≤ γ) (d ℓ Q M : ℕ) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hQpow : (Q : ℝ) ≤ (Q * M : ℕ) ^ (1 / 16 : ℝ)) :
    sparseCountError γ d ℓ Q M ≤
      sparseErrorLiftConstant γ d ℓ * (Q * M : ℕ) ^ (- (1 / 8 : ℝ)) := by
  have hLnat : 1 ≤ Q * M := by nlinarith
  have hL : (1 : ℝ) ≤ (Q * M : ℕ) := by exact_mod_cast hLnat
  have hLpos : (0 : ℝ) < (Q * M : ℕ) := lt_of_lt_of_le zero_lt_one hL
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hnum := sparse_error_numerator_le hγ hγlower hL d ℓ
  have hnorm : ((Q * M : ℕ) : ℝ) ^ (13 / 16 : ℝ) / M =
      (Q : ℝ) * ((Q * M : ℕ) : ℝ) ^ (- (3 / 16 : ℝ)) := by
    have hid : ((Q * M : ℕ) : ℝ) ^ (13 / 16 : ℝ) /
        ((Q * M : ℕ) : ℝ) = ((Q * M : ℕ) : ℝ) ^ (- (3 / 16 : ℝ)) := by
      rw [← Real.rpow_sub_one hLpos.ne']
      norm_num
    rw [← hid]
    push_cast
    field_simp
    ring
  calc
    sparseCountError γ d ℓ Q M ≤
        sparseErrorLiftConstant γ d ℓ * ((Q * M : ℕ) : ℝ) ^ (13 / 16 : ℝ) / M := by
      unfold sparseCountError
      apply div_le_div_of_nonneg_right _ hMpos.le
      simpa only [Nat.cast_add, Nat.cast_one] using hnum
    _ = sparseErrorLiftConstant γ d ℓ *
        ((Q : ℝ) * ((Q * M : ℕ) : ℝ) ^ (- (3 / 16 : ℝ))) := by
      rw [mul_div_assoc, hnorm]
    _ ≤ sparseErrorLiftConstant γ d ℓ *
        (((Q * M : ℕ) : ℝ) ^ (1 / 16 : ℝ) *
          ((Q * M : ℕ) : ℝ) ^ (- (3 / 16 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hQpow (by positivity))
        (sparseErrorLiftConstant_pos hγ d ℓ).le
    _ = _ := by rw [← Real.rpow_add hLpos]; norm_num

/-- Explicit saving in `N`, uniform over every subpower modulus. -/
theorem eventually_sparseCountError_power_bound {γ a : ℝ} (hγ : 0 < γ)
    (hγlower : 3 / 4 ≤ γ) (ha : a < 1) (d ℓ : ℕ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      sparseCountError γ d ℓ Q (floorScale N Q d) ≤
        (sparseErrorLiftConstant γ d ℓ * (2 : ℝ) ^ (1 / 8 : ℝ)) *
          (N : ℝ) ^ (- (1 / 8 : ℝ) / (d : ℝ)) := by
  filter_upwards [eventually_liftedScale_parameters ha
    (by norm_num : (0 : ℝ) < 1 / 16) d hd, eventually_ge_atTop 1] with N hp hN
  intro Q hQ hQR
  obtain ⟨hM, _, hQP⟩ := hp Q hQ hQR
  have he := sparseCountError_le_lifted_power hγ hγlower d ℓ Q (floorScale N Q d)
    hQ hM (by simpa only [liftedScale] using hQP)
  have htransfer := negative_rpow_liftedScale_le N Q d (by omega) (by omega) hd hM
    (1 / 8 : ℝ) (by norm_num)
  calc
    _ ≤ sparseErrorLiftConstant γ d ℓ * (liftedScale N Q d : ℝ) ^ (-(1 / 8 : ℝ)) := he
    _ ≤ sparseErrorLiftConstant γ d ℓ *
        ((2 : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ) / (d : ℝ))) :=
      mul_le_mul_of_nonneg_left htransfer (sparseErrorLiftConstant_pos hγ d ℓ).le
    _ = _ := by ring

/-- A fixed coefficient in the sublinear logarithmic exponential is harmless.
The threshold is selected before any modulus or density parameter. -/
theorem eventually_scaled_exp_log_subpower_le_rpow {a B ε : ℝ}
    (ha : a < 1) (hB : 0 < B) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (B * (Real.log (N : ℝ)) ^ a) ≤ (N : ℝ) ^ ε := by
  have h := tendsto_natCast_atTop_atTop.eventually
    (exp_log_subpower_le_rpow ha (div_pos hε hB))
  filter_upwards [h, eventually_gt_atTop 1] with N hN hNlarge
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  calc
    Real.exp (B * (Real.log (N : ℝ)) ^ a) =
        (Real.exp ((Real.log (N : ℝ)) ^ a)) ^ B := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    _ ≤ ((N : ℝ) ^ (ε / B)) ^ B :=
      Real.rpow_le_rpow (Real.exp_pos _).le hN hB.le
    _ = (N : ℝ) ^ ε := by
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      field_simp

/-- Every fixed power saving eventually beats the actual density and prime
mass lower bounds. The density is quantified after the common threshold. -/
theorem eventually_powerSaving_le_density_mass {a ν η C c b B : ℝ}
    (ha : a < 1) (hη : 0 < η) (hC : 0 < C) (hc : 0 < c)
    (hb : 0 < b) (hB : 0 < B) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ δ : ℝ,
      (Real.log (N : ℝ)) ^ (-ν) < δ →
      C * (N : ℝ) ^ (-η) ≤
        c * δ ^ k * b * Real.exp (-B * (Real.log (N : ℝ)) ^ a) := by
  have hcoef : 0 < C / (c * b) := div_pos hC (mul_pos hc hb)
  filter_upwards [eventually_const_log_rpow_lt_rpow (p := ν * k) hcoef
      (show 0 < η / 2 by positivity),
    eventually_scaled_exp_log_subpower_le_rpow ha hB
      (show 0 < η / 2 by positivity), eventually_gt_atTop 1]
    with N hpoly hexp hNlarge
  intro δ hδlower
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hNlarge)
  have hδ : 0 < δ := lt_trans (Real.rpow_pos_of_pos hlog _) hδlower
  have hδpow : (Real.log (N : ℝ)) ^ (-(ν * k)) ≤ δ ^ k := by
    calc
      _ = ((Real.log (N : ℝ)) ^ (-ν)) ^ k := by
        rw [← Real.rpow_mul_natCast hlog.le]
        congr 1
        ring
      _ ≤ δ ^ k := pow_le_pow_left₀ (Real.rpow_nonneg hlog.le _) hδlower.le _
  have hlogrecip : C * (N : ℝ) ^ (-(η / 2)) ≤
      (c * b) * (Real.log (N : ℝ)) ^ (-(ν * k)) := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_neg hlog.le]
    change C / (N : ℝ) ^ (η / 2) ≤ (c * b) / (Real.log (N : ℝ)) ^ (ν * k)
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hNpos _)
      (Real.rpow_pos_of_pos hlog _)).mpr
    calc
      C * (Real.log (N : ℝ)) ^ (ν * k) =
          ((C / (c * b)) * (Real.log (N : ℝ)) ^ (ν * k)) * (c * b) := by
        field_simp
      _ ≤ (N : ℝ) ^ (η / 2) * (c * b) :=
        mul_le_mul_of_nonneg_right hpoly.le (mul_pos hc hb).le
      _ = _ := by ring
  have hexprecip : (N : ℝ) ^ (-(η / 2)) ≤
      Real.exp (-B * (Real.log (N : ℝ)) ^ a) := by
    rw [Real.rpow_neg hNpos.le,
      show -B * (Real.log (N : ℝ)) ^ a = -(B * (Real.log (N : ℝ)) ^ a) by ring,
      Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hexp
  calc
    C * (N : ℝ) ^ (-η) =
        (C * (N : ℝ) ^ (-(η / 2))) * (N : ℝ) ^ (-(η / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hNpos]
      congr 2
      ring
    _ ≤ ((c * b) * (Real.log (N : ℝ)) ^ (-(ν * k))) *
        Real.exp (-B * (Real.log (N : ℝ)) ^ a) :=
      mul_le_mul hlogrecip hexprecip (Real.rpow_nonneg hNpos.le _) (by positivity)
    _ ≤ ((c * b) * δ ^ k) * Real.exp (-B * (Real.log (N : ℝ)) ^ a) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hδpow (mul_pos hc hb).le) (Real.exp_pos _).le
    _ = _ := by ring

end PSPrimes
