import Mathlib

/-!
# Exact floor-scale inequalities for Proposition 2.3

The manuscript sets `M = floor ((N / Q^(d-1))^(1/d))` and `L = Q*M`.
This module proves finite inequalities with explicit constants once `M ≥ 1`.
No asymptotic hypothesis on `Q` and no large-parameter threshold is assumed.
-/

noncomputable section

namespace PSPrimes

/-- The real scale before taking the natural-number floor. -/
def rootScale (N Q d : ℕ) : ℝ :=
  ((N : ℝ) / (Q : ℝ) ^ (d - 1)) ^ (1 / (d : ℝ))

/-- The integer parameter length from Proposition 2.3. -/
def floorScale (N Q d : ℕ) : ℕ := ⌊rootScale N Q d⌋₊

/-- The parameter length after restoring the fixed polynomial family. -/
def liftedScale (N Q d : ℕ) : ℕ := Q * floorScale N Q d

theorem rootScale_nonneg (N Q d : ℕ) : 0 ≤ rootScale N Q d := by
  unfold rootScale
  exact Real.rpow_nonneg (by positivity) _

/-- Raising the positive-degree root back to the integer degree is exact. -/
theorem rootScale_pow (N Q d : ℕ) (hd : 0 < d) :
    rootScale N Q d ^ d = (N : ℝ) / (Q : ℝ) ^ (d - 1) := by
  simpa [rootScale, one_div] using
    Real.rpow_inv_natCast_pow (x := (N : ℝ) / (Q : ℝ) ^ (d - 1))
      (by positivity) (Nat.ne_of_gt hd)

theorem floorScale_le_root (N Q d : ℕ) :
    (floorScale N Q d : ℝ) ≤ rootScale N Q d := by
  exact Nat.floor_le (rootScale_nonneg N Q d)

/-- The loss of a factor two follows solely from `M ≥ 1`. -/
theorem rootScale_lt_twice_floor (N Q d : ℕ) (hM : 1 ≤ floorScale N Q d) :
    rootScale N Q d < 2 * (floorScale N Q d : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (rootScale N Q d)
  have hMreal : (1 : ℝ) ≤ floorScale N Q d := by exact_mod_cast hM
  change rootScale N Q d < (floorScale N Q d : ℝ) + 1 at hfloor
  linarith

/-- Exact finite version of the comparison between `M^d` and `N/Q^(d-1)`. -/
theorem floorScale_power_bounds (N Q d : ℕ) (hd : 0 < d)
    (hM : 1 ≤ floorScale N Q d) :
    (floorScale N Q d : ℝ) ^ d ≤ (N : ℝ) / (Q : ℝ) ^ (d - 1) ∧
      (N : ℝ) / (Q : ℝ) ^ (d - 1) ≤ (2 * (floorScale N Q d : ℝ)) ^ d := by
  have hrootpow := rootScale_pow N Q d hd
  constructor
  · rw [← hrootpow]
    exact pow_le_pow_left₀ (by positivity) (floorScale_le_root N Q d) _
  · rw [← hrootpow]
    exact pow_le_pow_left₀ (rootScale_nonneg N Q d)
      (rootScale_lt_twice_floor N Q d hM).le _

/-- Exact constants for the manuscript's `L^d ≍ Q*N`. -/
theorem liftedScale_power_bounds (N Q d : ℕ) (hQ : 0 < Q) (hd : 0 < d)
    (hM : 1 ≤ floorScale N Q d) :
    (liftedScale N Q d : ℝ) ^ d ≤ (Q : ℝ) * (N : ℝ) ∧
      (Q : ℝ) * (N : ℝ) ≤ (2 : ℝ) ^ d * (liftedScale N Q d : ℝ) ^ d := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQpow : (Q : ℝ) ^ d = (Q : ℝ) * (Q : ℝ) ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ']
  obtain ⟨hlo, hhi⟩ := floorScale_power_bounds N Q d hd hM
  have hlo' := (le_div_iff₀ (pow_pos hQreal (d - 1))).mp hlo
  have hhi' := (div_le_iff₀ (pow_pos hQreal (d - 1))).mp hhi
  constructor
  · calc
      (liftedScale N Q d : ℝ) ^ d =
          (Q : ℝ) * ((floorScale N Q d : ℝ) ^ d * (Q : ℝ) ^ (d - 1)) := by
        simp only [liftedScale, Nat.cast_mul, mul_pow, hQpow]
        ring
      _ ≤ (Q : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left hlo' hQreal.le
  · calc
      (Q : ℝ) * (N : ℝ) ≤
          (Q : ℝ) * ((2 * (floorScale N Q d : ℝ)) ^ d * (Q : ℝ) ^ (d - 1)) :=
        mul_le_mul_of_nonneg_left hhi' hQreal.le
      _ = (2 : ℝ) ^ d * (liftedScale N Q d : ℝ) ^ d := by
        simp only [liftedScale, Nat.cast_mul, mul_pow, hQpow]
        ring

/-- Cancellation of the positive floor parameter in the lifted normalization. -/
theorem liftedScale_normalization_identity (N Q d : ℕ) (hN : 0 < N)
    (hM : 1 ≤ floorScale N Q d) :
    (liftedScale N Q d : ℝ) ^ (d + 1) /
        ((N : ℝ) * (floorScale N Q d : ℝ)) =
      (Q : ℝ) * (liftedScale N Q d : ℝ) ^ d / (N : ℝ) := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hMreal : (floorScale N Q d : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : floorScale N Q d ≠ 0)
  rw [pow_succ]
  simp only [liftedScale, Nat.cast_mul]
  field_simp
  ring

/-- Exact two-sided form of `L^(d+1)/(N*M) ≍ Q²`.
The upper bound is `Q²`, and the lower constant is `2^(-d)`. -/
theorem liftedScale_normalization_bounds (N Q d : ℕ) (hN : 0 < N)
    (hQ : 0 < Q) (hd : 0 < d) (hM : 1 ≤ floorScale N Q d) :
    (Q : ℝ) ^ 2 / (2 : ℝ) ^ d ≤
        (liftedScale N Q d : ℝ) ^ (d + 1) /
          ((N : ℝ) * (floorScale N Q d : ℝ)) ∧
      (liftedScale N Q d : ℝ) ^ (d + 1) /
          ((N : ℝ) * (floorScale N Q d : ℝ)) ≤ (Q : ℝ) ^ 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hQreal : (0 : ℝ) ≤ Q := by positivity
  have htwo : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  obtain ⟨hlo, hhi⟩ := liftedScale_power_bounds N Q d hQ hd hM
  rw [liftedScale_normalization_identity N Q d hN hM]
  constructor
  · apply (div_le_div_iff₀ htwo hNreal).mpr
    have h := mul_le_mul_of_nonneg_left hhi hQreal
    nlinarith [h]
  · apply (div_le_iff₀ hNreal).mpr
    have h := mul_le_mul_of_nonneg_left hlo hQreal
    nlinarith [h]

/-- A function supported at scale `C₀*N` dilates into the fixed-family
scale with the explicit support constant `C₀*2^d`. -/
theorem dilated_support_scale_le (N Q d : ℕ) (hQ : 0 < Q) (hd : 0 < d)
    (hM : 1 ≤ floorScale N Q d) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    (Q : ℝ) * C₀ * (N : ℝ) ≤
      (C₀ * (2 : ℝ) ^ d) * (liftedScale N Q d : ℝ) ^ d := by
  have h := mul_le_mul_of_nonneg_left
    (liftedScale_power_bounds N Q d hQ hd hM).2 hC₀
  nlinarith [h]

end PSPrimes
