import PSPrimes.Scales
import PSPrimes.Asymptotics
import PSPrimes.PowerSaving

/-!
# Uniform asymptotic consequences of the subpower modulus range

All thresholds below are chosen before quantifying over `Q`. They therefore
apply uniformly to every positive modulus in the manuscript's range
`Q ≤ exp((log N)^a)`. The constants may depend on `a`, `d`, and the displayed
positive exponent or fixed target floor length.
-/

noncomputable section
open Filter Topology

namespace PSPrimes

/-- A finite sufficient condition for the floor parameter to be positive. -/
theorem floorScale_pos_of_modulus_le_root (N Q d : ℕ) (hN : 1 ≤ N)
    (hQ : 1 ≤ Q) (hd : 0 < d)
    (hQR : (Q : ℝ) ≤ (N : ℝ) ^ (1 / (d : ℝ))) :
    1 ≤ floorScale N Q d := by
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hrootpow : ((N : ℝ) ^ (1 / (d : ℝ))) ^ d = (N : ℝ) := by
    simpa [one_div] using Real.rpow_inv_natCast_pow
      (x := (N : ℝ)) (by positivity) (Nat.ne_of_gt hd)
  have hpow : (Q : ℝ) ^ d ≤ (N : ℝ) := by
    rw [← hrootpow]
    exact pow_le_pow_left₀ (by positivity) hQR _
  have hpowprev : (Q : ℝ) ^ (d - 1) ≤ (N : ℝ) :=
    (pow_le_pow_right₀ hQone (Nat.sub_le d 1)).trans hpow
  have hbase : (1 : ℝ) ≤ (N : ℝ) / (Q : ℝ) ^ (d - 1) := by
    exact (le_div_iff₀ (pow_pos hQpos _)).mpr (by simpa using hpowprev)
  have hroot : (1 : ℝ) ≤ rootScale N Q d := by
    exact Real.one_le_rpow hbase (by positivity)
  exact (Nat.le_floor_iff (rootScale_nonneg N Q d)).mpr (by simpa using hroot)

/-- For positive input length and modulus, the floor length does not exceed
`N`. Thus a lower threshold on `M` also forces the same lower threshold on `N`. -/
theorem floorScale_le_length (N Q d : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hd : 0 < d) : floorScale N Q d ≤ N := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hbase : (N : ℝ) / (Q : ℝ) ^ (d - 1) ≤ (N : ℝ) :=
    div_le_self (by positivity) (one_le_pow₀ hQreal)
  have hexp : (1 : ℝ) / (d : ℝ) ≤ 1 := (div_le_one hdpos).mpr hdreal
  have hroot : rootScale N Q d ≤ (N : ℝ) := by
    calc
      rootScale N Q d ≤ (N : ℝ) ^ (1 / (d : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ ≤ (N : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le hNreal hexp
  have hfloor : (floorScale N Q d : ℝ) ≤ (N : ℝ) :=
    (floorScale_le_root N Q d).trans hroot
  exact_mod_cast hfloor

/-- The floor length is eventually positive, uniformly over the modulus. -/
theorem eventually_floorScale_pos {a : ℝ} (ha : a < 1) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      1 ≤ floorScale N Q d := by
  have he : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  filter_upwards [modulus_subpower ha he, eventually_ge_atTop 1] with N hsub hN
  intro Q hQ hQR
  exact floorScale_pos_of_modulus_le_root N Q d hN hQ hd (hsub Q hQR)

/-- The lifted scale grows at least like `N^(1/(2d))` uniformly in `Q`. -/
theorem eventually_liftedScale_lower {a : ℝ} (ha : a < 1) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      (N : ℝ) ^ (1 / (2 * (d : ℝ))) ≤ (liftedScale N Q d : ℝ) := by
  have hβ : (0 : ℝ) < 1 / (2 * (d : ℝ)) := by positivity
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / (2 * (d : ℝ)))) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_floorScale_pos ha d hd, ht.eventually_ge_atTop 2,
    eventually_ge_atTop 1] with N hfloor hlarge hN
  intro Q hQ hQR
  have hroot := rootScale_le_twice_lifted N Q d (by omega) hd (hfloor Q hQ hQR)
  have hid : (N : ℝ) ^ (1 / (d : ℝ)) =
      ((N : ℝ) ^ (1 / (2 * (d : ℝ)))) ^ 2 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    field_simp
  rw [hid] at hroot
  nlinarith

/-- Every subpower modulus is eventually smaller than any prescribed
positive power of the lifted scale, uniformly in the modulus. -/
theorem eventually_modulus_le_liftedScale_rpow {a δ : ℝ} (ha : a < 1)
    (hδ : 0 < δ) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      (Q : ℝ) ≤ (liftedScale N Q d : ℝ) ^ δ := by
  have he : (0 : ℝ) < δ / (2 * (d : ℝ)) := by positivity
  filter_upwards [modulus_subpower ha he, eventually_liftedScale_lower ha d hd]
    with N hsub hscale
  intro Q hQ hQR
  calc
    (Q : ℝ) ≤ (N : ℝ) ^ (δ / (2 * (d : ℝ))) := hsub Q hQR
    _ = ((N : ℝ) ^ (1 / (2 * (d : ℝ)))) ^ δ := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      ring
    _ ≤ (liftedScale N Q d : ℝ) ^ δ :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
        (hscale Q hQ hQR) hδ.le

/-- The manuscript's "sufficiently large `M`" condition can be met uniformly
throughout the full subpower-modulus range, for every fixed target length. -/
theorem eventually_floorScale_ge {a : ℝ} (ha : a < 1) (d : ℕ) (hd : 0 < d)
    (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      K ≤ floorScale N Q d := by
  have hε : (0 : ℝ) < 1 / (4 * (d : ℝ)) := by positivity
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / (4 * (d : ℝ)))) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [modulus_subpower ha hε, eventually_liftedScale_lower ha d hd,
    ht.eventually_ge_atTop (K : ℝ), eventually_ge_atTop 1]
    with N hsub hscale hK hN
  intro Q hQ hQR
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hprod : (Q : ℝ) * (K : ℝ) ≤
      (Q : ℝ) * (floorScale N Q d : ℝ) := by
    calc
      (Q : ℝ) * (K : ℝ) ≤
          (N : ℝ) ^ (1 / (4 * (d : ℝ))) *
            (N : ℝ) ^ (1 / (4 * (d : ℝ))) :=
        mul_le_mul (hsub Q hQR) hK (by positivity) (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (1 / (2 * (d : ℝ))) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        field_simp
        ring
      _ ≤ (Q : ℝ) * (floorScale N Q d : ℝ) := by
        simpa only [liftedScale, Nat.cast_mul] using hscale Q hQ hQR
  have hreal := (mul_le_mul_left hQpos).mp hprod
  exact_mod_cast hreal

/-- Joint parameter package; its threshold is independent of `Q`. -/
theorem eventually_liftedScale_parameters {a δ : ℝ} (ha : a < 1)
    (hδ : 0 < δ) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      1 ≤ floorScale N Q d ∧
        (N : ℝ) ^ (1 / (2 * (d : ℝ))) ≤ (liftedScale N Q d : ℝ) ∧
        (Q : ℝ) ≤ (liftedScale N Q d : ℝ) ^ δ := by
  filter_upwards [eventually_floorScale_pos ha d hd,
    eventually_liftedScale_lower ha d hd,
    eventually_modulus_le_liftedScale_rpow ha hδ d hd] with N hM hL hQ
  intro Q hQpos hQR
  exact ⟨hM Q hQpos hQR, hL Q hQpos hQR, hQ Q hQpos hQR⟩

end PSPrimes
