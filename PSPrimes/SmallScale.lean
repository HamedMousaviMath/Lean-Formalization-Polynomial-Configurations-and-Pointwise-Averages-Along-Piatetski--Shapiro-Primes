import PSPrimes.AsymptoticScales
import PSPrimes.RecurrenceDefinitions

/-!
# Uniform elimination of the weak-regularity small-scale alternative

All eventual thresholds precede the modulus and density parameters. The
estimates are consequences of the explicit subpower modulus and logarithmic
density ranges, not assumptions asserting that the regularity alternative
has already been eliminated.
-/

noncomputable section
open Filter Topology

namespace PSPrimes

/-- A fixed logarithmic power, with a fixed multiplicative constant, is
strictly smaller than any positive power for all sufficiently large integers. -/
theorem eventually_const_log_rpow_lt_rpow {C p s : ℝ} (hC : 0 < C) (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, C * (Real.log (N : ℝ)) ^ p < (N : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop p hs).def
    (show 0 < 1 / (2 * C) by positivity)
  have hn := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hn, eventually_gt_atTop 1] with N hN hNlarge
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hNlarge)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hN
  have hmul := mul_le_mul_of_nonneg_left hN hC.le
  have hid : C * (1 / (2 * C)) = (1 / 2 : ℝ) := by field_simp; ring
  rw [← mul_assoc, hid] at hmul
  have hpos := Real.rpow_pos_of_pos hNpos s
  nlinarith

/-- The regularity small-scale upper bound is uniformly subpower.
The bound does not require `δ ≤ 1`; the manuscript's smaller density range
is therefore a valid direct application. -/
theorem small_scale_alternative_excluded {a b k e₀ Csmall A ρ : ℝ}
    (ha : a < 1) (_hb : 0 < b) (hk : 0 < k) (he₀ : 0 < e₀)
    (hC : 0 < Csmall) (hA : 0 < A) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q → ∀ δ : ℝ,
      (Real.log (N : ℝ)) ^ (-b) < δ →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      Csmall * ((Q : ℝ) / (e₀ * δ ^ k)) ^ A < (N : ℝ) ^ ρ := by
  have hsubexp : 0 < ρ / (2 * A) := by positivity
  have hcoef : 0 < Csmall / e₀ ^ A := div_pos hC (Real.rpow_pos_of_pos he₀ _)
  filter_upwards [modulus_subpower ha hsubexp,
    eventually_const_log_rpow_lt_rpow (p := b * k * A) hcoef
      (show 0 < ρ / 2 by positivity), eventually_gt_atTop 1]
    with N hsub hpoly hNlarge
  intro Q hQ δ hδlower hQR
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hNlarge)
  have hδ : 0 < δ := lt_trans (Real.rpow_pos_of_pos hlog _) hδlower
  have hδinv : δ ^ (-k) ≤ (Real.log (N : ℝ)) ^ (b * k) := by
    calc
      δ ^ (-k) ≤ ((Real.log (N : ℝ)) ^ (-b)) ^ (-k) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hlog _)
          hδlower.le (by linarith)
      _ = (Real.log (N : ℝ)) ^ (b * k) := by
        rw [← Real.rpow_mul hlog.le]
        congr 1
        ring
  have hbase : (Q : ℝ) / (e₀ * δ ^ k) ≤
      ((Q : ℝ) / e₀) * (Real.log (N : ℝ)) ^ (b * k) := by
    calc
      (Q : ℝ) / (e₀ * δ ^ k) = ((Q : ℝ) / e₀) * δ ^ (-k) := by
        rw [Real.rpow_neg hδ.le]
        ring
      _ ≤ ((Q : ℝ) / e₀) * (Real.log (N : ℝ)) ^ (b * k) :=
        mul_le_mul_of_nonneg_left hδinv (div_nonneg hQpos.le he₀.le)
  have hQpow : (Q : ℝ) ^ A ≤ (N : ℝ) ^ (ρ / 2) := by
    calc
      (Q : ℝ) ^ A ≤ ((N : ℝ) ^ (ρ / (2 * A))) ^ A :=
        Real.rpow_le_rpow hQpos.le (hsub Q hQR) hA.le
      _ = (N : ℝ) ^ (ρ / 2) := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1
        field_simp
        ring
  have hfactor : 0 ≤ (Csmall / e₀ ^ A) * (Real.log (N : ℝ)) ^ (b * k * A) :=
    mul_nonneg hcoef.le (Real.rpow_nonneg hlog.le _)
  calc
    Csmall * ((Q : ℝ) / (e₀ * δ ^ k)) ^ A ≤
        Csmall * (((Q : ℝ) / e₀) * (Real.log (N : ℝ)) ^ (b * k)) ^ A :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hbase hA.le) hC.le
    _ = (Q : ℝ) ^ A *
        ((Csmall / e₀ ^ A) * (Real.log (N : ℝ)) ^ (b * k * A)) := by
      rw [Real.mul_rpow (div_nonneg hQpos.le he₀.le) (Real.rpow_nonneg hlog.le _),
        Real.div_rpow hQpos.le he₀.le, ← Real.rpow_mul hlog.le]
      ring
    _ ≤ (N : ℝ) ^ (ρ / 2) *
        ((Csmall / e₀ ^ A) * (Real.log (N : ℝ)) ^ (b * k * A)) :=
      mul_le_mul_of_nonneg_right hQpow hfactor
    _ < (N : ℝ) ^ (ρ / 2) * (N : ℝ) ^ (ρ / 2) :=
      mul_lt_mul_of_pos_left hpoly (Real.rpow_pos_of_pos hNpos _)
    _ = (N : ℝ) ^ ρ := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

/-- Natural-exponent version matching the regularity source's interface. -/
theorem small_scale_alternative_excluded_nat {a b e₀ Csmall ρ : ℝ}
    (ha : a < 1) (hb : 0 < b) (he₀ : 0 < e₀) (hC : 0 < Csmall) (hρ : 0 < ρ)
    (k A : ℕ) (hk : 1 ≤ k) (hA : 1 ≤ A) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q → ∀ δ : ℝ,
      (Real.log (N : ℝ)) ^ (-b) < δ →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      Csmall * ((Q : ℝ) / (e₀ * δ ^ k)) ^ A < (N : ℝ) ^ ρ := by
  simpa only [Real.rpow_natCast] using
    (small_scale_alternative_excluded (k := (k : ℝ)) (A := (A : ℝ))
      ha hb (by exact_mod_cast (by omega : 0 < k)) he₀ hC
      (by exact_mod_cast (by omega : 0 < A)) hρ)

/-- The integer floor scale itself retains a uniform positive power of `N`.
This supplements the lifted-scale lower bound, and retains its factor of `Q`. -/
theorem eventually_floorScale_rpow_lower {a : ℝ} (ha : a < 1)
    (d : ℕ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      (N : ℝ) ^ (1 / (4 * (d : ℝ))) ≤ (floorScale N Q d : ℝ) := by
  have hε : (0 : ℝ) < 1 / (4 * (d : ℝ)) := by positivity
  filter_upwards [modulus_subpower ha hε, eventually_liftedScale_lower ha d hd,
    eventually_ge_atTop 1] with N hsub hscale hN
  intro Q hQ hQR
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hprod : (Q : ℝ) * (N : ℝ) ^ (1 / (4 * (d : ℝ))) ≤
      (Q : ℝ) * (floorScale N Q d : ℝ) := by
    calc
      (Q : ℝ) * (N : ℝ) ^ (1 / (4 * (d : ℝ))) ≤
          (N : ℝ) ^ (1 / (4 * (d : ℝ))) *
            (N : ℝ) ^ (1 / (4 * (d : ℝ))) :=
        mul_le_mul_of_nonneg_right (hsub Q hQR) (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (1 / (2 * (d : ℝ))) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        field_simp
        ring
      _ ≤ (Q : ℝ) * (floorScale N Q d : ℝ) := by
        simpa only [liftedScale, Nat.cast_mul] using hscale Q hQ hQR
  exact (mul_le_mul_left hQpos).mp hprod

/-- Above an explicit finite threshold, the truncation factor loses at most
a square root. This is an elementary estimate, not an asymptotic input. -/
theorem rpow_half_le_truncated_scale {x : ℝ} (hx : Real.exp 4 ≤ x) :
    x ^ (1 / 2 : ℝ) ≤ x * Real.exp (-Real.sqrt (Real.log x)) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx
  have hlog : (4 : ℝ) ≤ Real.log x := by
    calc
      (4 : ℝ) = Real.log (Real.exp 4) := by simp
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 4) hx
  have hsq := Real.sq_sqrt (show 0 ≤ Real.log x by linarith)
  have hs0 := Real.sqrt_nonneg (Real.log x)
  have hs2 : (2 : ℝ) ≤ Real.sqrt (Real.log x) := by nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr hs2) hs0
  have hsqrt : Real.sqrt (Real.log x) ≤ Real.log x / 2 := by nlinarith
  calc
    x ^ (1 / 2 : ℝ) = Real.exp (Real.log x * (1 / 2 : ℝ)) :=
      Real.rpow_def_of_pos hxpos _
    _ = Real.exp (Real.log x) * Real.exp (-(Real.log x) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = x * Real.exp (-(Real.log x) / 2) := by rw [Real.exp_log hxpos]
    _ ≤ x * Real.exp (-Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hxpos.le

/-- The actual truncated parameter from KMTT remains above a fixed power
of `N`, uniformly in every allowed modulus. The exponent `1/(8d)` is an
explicit sufficient lower bound; no sharper manuscript display is claimed. -/
theorem eventually_truncated_floorScale_lower {a : ℝ} (ha : a < 1)
    (d : ℕ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) → ∀ M₀ : ℕ,
      ⌈(floorScale N Q d : ℝ) *
        Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ)))⌉₊ ≤ M₀ →
      (N : ℝ) ^ (1 / (8 * (d : ℝ))) ≤ (M₀ : ℝ) := by
  have hβ : (0 : ℝ) < 1 / (4 * (d : ℝ)) := by positivity
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / (4 * (d : ℝ)))) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_floorScale_rpow_lower ha d hd,
    ht.eventually_ge_atTop (Real.exp 4), eventually_ge_atTop 1]
    with N hscale hlarge hN
  intro Q hQ hQR M₀ hM₀
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMlower := hscale Q hQ hQR
  have hMlarge : Real.exp 4 ≤ (floorScale N Q d : ℝ) := hlarge.trans hMlower
  calc
    (N : ℝ) ^ (1 / (8 * (d : ℝ))) =
        ((N : ℝ) ^ (1 / (4 * (d : ℝ)))) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      field_simp
      ring
    _ ≤ (floorScale N Q d : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hMlower (by norm_num)
    _ ≤ (floorScale N Q d : ℝ) *
        Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ))) :=
      rpow_half_le_truncated_scale hMlarge
    _ ≤ (M₀ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hM₀)

/-- Joint natural-exponent form: the literal KMTT small-scale branch is
impossible throughout the admissible modulus/density range at large `N`. -/
theorem eventually_not_small_scale_alternative {a b e₀ Csmall : ℝ}
    (ha : a < 1) (hb : 0 < b) (he₀ : 0 < e₀) (hC : 0 < Csmall)
    (d k A : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hA : 1 ≤ A) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q → ∀ δ : ℝ,
      (Real.log (N : ℝ)) ^ (-b) < δ →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) → ∀ M₀ : ℕ,
      ⌈(floorScale N Q d : ℝ) *
        Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ)))⌉₊ ≤ M₀ →
      ¬((M₀ : ℝ) ≤ Csmall * ((Q : ℝ) / (e₀ * δ ^ k)) ^ A) := by
  have hρ : (0 : ℝ) < 1 / (8 * (d : ℝ)) := by positivity
  filter_upwards [small_scale_alternative_excluded_nat ha hb he₀ hC hρ k A hk hA,
    eventually_truncated_floorScale_lower ha d (by omega)] with N hsmall hlarge
  intro Q hQ δ hδ hQR M₀ htrunc hbranch
  have hs := hsmall Q hQ δ hδ hQR
  have hl := hlarge Q hQ hQR M₀ htrunc
  linarith

end PSPrimes
