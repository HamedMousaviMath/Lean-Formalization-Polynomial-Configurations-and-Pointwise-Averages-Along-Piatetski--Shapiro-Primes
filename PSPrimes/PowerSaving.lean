import PSPrimes.Comparison
import PSPrimes.Scales
import PSPrimes.Asymptotics

/-!
# Explicit absorption of the finite comparison bound

This module keeps all exponents and constants visible. In particular no
Piatetski--Shapiro comparison conclusion is added as an input.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- Split the sublinear power in the finite comparison estimate. -/
theorem weighted_root_sum_le {L B E t : ℝ}
    (hL : 0 < L) (hB : 0 < B) (hE : 0 ≤ E)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    B * (L⁻¹ + E / B) ^ t ≤
      B * L ^ (-t) + B ^ (1 - t) * E ^ t := by
  have hsplit := Real.rpow_add_le_add_rpow (inv_nonneg.mpr hL.le)
    (div_nonneg hE hB.le) ht₀ ht₁
  have hfirst : L⁻¹ ^ t = L ^ (-t) := by
    rw [Real.inv_rpow hL.le, Real.rpow_neg hL.le]
  have hsecond : B * (E / B) ^ t = B ^ (1 - t) * E ^ t := by
    rw [Real.div_rpow hE hB.le, Real.rpow_sub hB, Real.rpow_one]
    ring
  calc
    _ ≤ B * (L⁻¹ ^ t + (E / B) ^ t) :=
      mul_le_mul_of_nonneg_left hsplit hB.le
    _ = _ := by rw [mul_add, hfirst, hsecond]

/-- Replace the weight and phase bounds by explicit powers, retaining both
constants and the two distinct exponent conditions. -/
theorem weighted_root_power_bound {L B E C A ε σ t : ℝ}
    (hL : 0 < L) (hB : 0 < B) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hBpow : B ≤ C * L ^ (2 * ε)) (hEpow : E ≤ A * L ^ (-σ)) :
    B * (L⁻¹ + E / B) ^ t ≤
      C * L ^ (2 * ε - t) +
        (C ^ (1 - t) * A ^ t) * L ^ (2 * ε * (1 - t) - σ * t) := by
  apply (weighted_root_sum_le hL hB hE ht₀ ht₁).trans
  apply add_le_add
  · calc
      B * L ^ (-t) ≤ (C * L ^ (2 * ε)) * L ^ (-t) :=
        mul_le_mul_of_nonneg_right hBpow (Real.rpow_nonneg hL.le _)
      _ = C * L ^ (2 * ε - t) := by rw [mul_assoc, ← Real.rpow_add hL]; rfl
  · calc
      B ^ (1 - t) * E ^ t ≤
          (C * L ^ (2 * ε)) ^ (1 - t) * (A * L ^ (-σ)) ^ t := by
        exact mul_le_mul
          (Real.rpow_le_rpow hB.le hBpow (by linarith))
          (Real.rpow_le_rpow hE hEpow ht₀)
          (Real.rpow_nonneg hE _) (Real.rpow_nonneg (by positivity) _)
      _ = (C ^ (1 - t) * A ^ t) * L ^ (2 * ε * (1 - t) - σ * t) := by
        rw [Real.mul_rpow hC (Real.rpow_nonneg hL.le _),
          Real.mul_rpow hA (Real.rpow_nonneg hL.le _),
          ← Real.rpow_mul hL.le, ← Real.rpow_mul hL.le]
        rw [show 2 * ε * (1 - t) - σ * t =
          (2 * ε) * (1 - t) + (-σ) * t by ring, Real.rpow_add hL]
        ring

/-- Two saving inequalities, isolated from all real-power manipulations. -/
theorem root_exponent_savings {ε σ s t : ℝ}
    (hε : 0 ≤ ε) (ht₀ : 0 ≤ t)
    (hs₁ : s ≤ 1) (hsσ : s ≤ σ) (hsmall : 8 * ε ≤ s * t) :
    2 * ε - t ≤ -(s * t) / 2 ∧
      2 * ε * (1 - t) - σ * t ≤ -(s * t) / 2 := by
  have hst : s * t ≤ t := by nlinarith
  have hσt : s * t ≤ σ * t := mul_le_mul_of_nonneg_right hsσ ht₀
  have hεt : 0 ≤ ε * t := mul_nonneg hε ht₀
  constructor <;> nlinarith

/-- Both terms are dominated by one negative power once ε is sufficiently
small. The constants need not be one and remain explicit. -/
theorem weighted_root_saving {L B E C A ε σ s t : ℝ}
    (hL : 1 ≤ L) (hB : 0 < B) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₁ : s ≤ 1) (hsσ : s ≤ σ)
    (hsmall : 8 * ε ≤ s * t)
    (hBpow : B ≤ C * L ^ (2 * ε)) (hEpow : E ≤ A * L ^ (-σ)) :
    B * (L⁻¹ + E / B) ^ t ≤
      (C + C ^ (1 - t) * A ^ t) * L ^ (-(s * t) / 2) := by
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hexp := root_exponent_savings hε ht₀ hs₁ hsσ hsmall
  apply (weighted_root_power_bound hL₀ hB hE hC hA ht₀ ht₁ hBpow hEpow).trans
  calc
    _ ≤ C * L ^ (-(s * t) / 2) +
        (C ^ (1 - t) * A ^ t) * L ^ (-(s * t) / 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL hexp.1) hC
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL hexp.2)
          (mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg hA _))
    _ = _ := by ring

/-- Absorb the precise Q² loss from the two-variable lift. -/
theorem weighted_root_modulus_saving {L Q B E C A ε σ s t : ℝ}
    (hL : 1 ≤ L) (hQ₀ : 0 ≤ Q) (hB : 0 < B) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₁ : s ≤ 1) (hsσ : s ≤ σ)
    (hsmall : 8 * ε ≤ s * t)
    (hBpow : B ≤ C * L ^ (2 * ε)) (hEpow : E ≤ A * L ^ (-σ))
    (hQ : Q ≤ L ^ (s * t / 8)) :
    Q ^ 2 * (B * (L⁻¹ + E / B) ^ t) ≤
      (C + C ^ (1 - t) * A ^ t) * L ^ (-(s * t) / 4) := by
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hcoeff : 0 ≤ C + C ^ (1 - t) * A ^ t :=
    add_nonneg hC (mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg hA _))
  have hQsq : Q ^ 2 ≤ L ^ (s * t / 4) := by
    calc
      _ ≤ (L ^ (s * t / 8)) ^ 2 := pow_le_pow_left₀ hQ₀ hQ 2
      _ = L ^ (s * t / 4) := by
        rw [← Real.rpow_mul_natCast hL₀.le]
        congr 1
        norm_num
        ring
  calc
    _ ≤ Q ^ 2 * ((C + C ^ (1 - t) * A ^ t) * L ^ (-(s * t) / 2)) :=
      mul_le_mul_of_nonneg_left
        (weighted_root_saving hL hB hE hC hA hε ht₀ ht₁ hs₁ hsσ hsmall hBpow hEpow)
        (sq_nonneg Q)
    _ ≤ L ^ (s * t / 4) *
        ((C + C ^ (1 - t) * A ^ t) * L ^ (-(s * t) / 2)) :=
      mul_le_mul_of_nonneg_right hQsq
        (mul_nonneg hcoeff (Real.rpow_nonneg hL₀.le _))
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hL₀]
      congr 2
      ring

/-- An explicit global logarithmic absorption, with the constant depending on
ε. This avoids an unspecified large-L threshold for the weight envelope. -/
theorem log_envelope_power_bound {G L ε : ℝ}
    (hG : 0 ≤ G) (hL : 1 ≤ L) (hε : 0 < ε) :
    G * (L + 1) ^ ε * Real.log (L + 1) ≤
      (G / ε * (2 : ℝ) ^ (2 * ε)) * L ^ (2 * ε) := by
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hX : 0 < L + 1 := by linarith
  calc
    _ ≤ G * (L + 1) ^ ε * ((L + 1) ^ ε / ε) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hX.le hε)
        (mul_nonneg hG (Real.rpow_nonneg hX.le _))
    _ = (G / ε) * (L + 1) ^ (2 * ε) := by
      rw [show 2 * ε = ε + ε by ring, Real.rpow_add hX]
      ring
    _ ≤ (G / ε) * (2 * L) ^ (2 * ε) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hG hε.le)
      exact Real.rpow_le_rpow hX.le (by linarith) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL₀.le]; ring

theorem phase_error_normalization (L A σ : ℝ) (hL : 0 < L) :
    A * L ^ (1 - σ) / L = A * L ^ (-σ) := by
  rw [mul_div_assoc, ← Real.rpow_sub_one hL.ne']
  congr 2
  ring

/-- The exact root-scale lower bound, before any eventual weakening. -/
theorem rootScale_le_twice_lifted (N Q d : ℕ) (hQ : 0 < Q) (hd : 0 < d)
    (hM : 1 ≤ floorScale N Q d) :
    (N : ℝ) ^ (1 / (d : ℝ)) ≤ 2 * (liftedScale N Q d : ℝ) := by
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hNQ : (N : ℝ) ≤ (Q : ℝ) * (N : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hQreal (Nat.cast_nonneg N)
  have hbound : (N : ℝ) ≤ (2 * (liftedScale N Q d : ℝ)) ^ d := by
    calc
      _ ≤ (Q : ℝ) * N := hNQ
      _ ≤ (2 : ℝ) ^ d * (liftedScale N Q d : ℝ) ^ d :=
        (liftedScale_power_bounds N Q d hQ hd hM).2
      _ = _ := (mul_pow _ _ _).symm
  have hinv : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have h := Real.rpow_le_rpow (Nat.cast_nonneg N) hbound hinv
  simpa only [one_div, Real.pow_rpow_inv_natCast (by positivity :
    (0 : ℝ) ≤ 2 * (liftedScale N Q d : ℝ)) (Nat.ne_of_gt hd)] using h

/-- Transfer any negative power at the lifted scale back to the manuscript's
integer scale, with the explicit factor 2^η. -/
theorem negative_rpow_liftedScale_le (N Q d : ℕ) (hN : 0 < N)
    (hQ : 0 < Q) (hd : 0 < d) (hM : 1 ≤ floorScale N Q d)
    (η : ℝ) (hη : 0 ≤ η) :
    (liftedScale N Q d : ℝ) ^ (-η) ≤
      (2 : ℝ) ^ η * (N : ℝ) ^ (-η / (d : ℝ)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hroot : 0 < (N : ℝ) ^ (1 / (d : ℝ)) :=
    Real.rpow_pos_of_pos hNreal _
  have hrootle : (N : ℝ) ^ (1 / (d : ℝ)) / 2 ≤ liftedScale N Q d := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have h := rootScale_le_twice_lifted N Q d hQ hd hM
    nlinarith
  calc
    _ ≤ ((N : ℝ) ^ (1 / (d : ℝ)) / 2) ^ (-η) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hrootle (by linarith)
    _ = (2 : ℝ) ^ η * (N : ℝ) ^ (-η / (d : ℝ)) := by
      rw [Real.div_rpow hroot.le (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul hNreal.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul]
      rw [mul_comm]
      congr 2
      ring

/-- A fixed-exponent quantitative version of the comparison at the exact
manuscript floor scale. All analytic hypotheses are the generic finite VN
estimate and the previously established progression-phase bound. This preserves
the chosen K, allowing the outer theorem to choose it before the family. -/
theorem ps_counting_comparison_power_bound {ℓ : ℕ}
    (N Q d K : ℕ) (hN : 0 < N) (hQ : 0 < Q) (hd : 0 < d)
    (hM : 1 ≤ floorScale N Q d) (hK : 1 ≤ K)
    (P : Fin ℓ → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (γ σ s A C : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 < s) (hs₁ : s ≤ 1) (hsσ : s ≤ σ)
    (hsmall : 8 * (1 - γ) ≤ s * (1 / (K : ℝ)))
    (hQpow : (Q : ℝ) ≤ (liftedScale N Q d : ℝ) ^ (s * (1 / (K : ℝ)) / 8))
    (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ)
    (hVN : ∀ (θ : ℕ → ℂ) (E : ℝ),
      (∀ n ∈ initialInterval (liftedScale N Q d), ‖θ n‖ ≤ 1) →
      0 ≤ E → PhaseBound d (liftedScale N Q d) θ
        ((liftedScale N Q d : ℝ) * E) →
      ‖polynomialForm (liftedScale N Q d) d P θ
          (liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀)
          (fun i => liftFunction (Q : ℤ) (f i))‖ ≤
        C * ((liftedScale N Q d : ℝ)⁻¹ + E) ^ (1 / (K : ℝ)))
    (hphase : PhaseBound d (floorScale N Q d)
      (fun y => (discrepancyWeight γ (Q * y + 1) : ℂ))
      (A * (liftedScale N Q d : ℝ) ^ (1 - σ))) :
    let t : ℝ := 1 / (K : ℝ)
    let C_B : ℝ := (γ⁻¹ + 1) / (1 - γ) * (2 : ℝ) ^ (2 * (1 - γ))
    ‖countingForm N (floorScale N Q d) Q (fun i => rescale (P i) (Q : ℤ))
        (fun n => (discrepancyWeight γ n : ℂ)) f₀ f‖ ≤
      (C * (C_B + C_B ^ (1 - t) * A ^ t) * (2 : ℝ) ^ (s * t / 4)) *
        (N : ℝ) ^ (-(s * t / 4) / (d : ℝ)) := by
  let M := floorScale N Q d
  let L := liftedScale N Q d
  let t : ℝ := 1 / (K : ℝ)
  let B : ℝ := (γ⁻¹ + 1) * ((L + 1 : ℕ) : ℝ) ^ (1 - γ) *
    Real.log ((L + 1 : ℕ) : ℝ)
  let E : ℝ := A * (L : ℝ) ^ (1 - σ) / L
  let C_B : ℝ := (γ⁻¹ + 1) / (1 - γ) * (2 : ℝ) ^ (2 * (1 - γ))
  change ‖countingForm N M Q (fun i => rescale (P i) (Q : ℤ))
    (fun n => (discrepancyWeight γ n : ℂ)) f₀ f‖ ≤
      (C * (C_B + C_B ^ (1 - t) * A ^ t) * (2 : ℝ) ^ (s * t / 4)) *
        (N : ℝ) ^ (-(s * t / 4) / (d : ℝ))
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ht₀ : 0 < t := one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hKreal)
  have ht₁ : t ≤ 1 := (div_le_one (lt_of_lt_of_le zero_lt_one hKreal)).mpr hKreal
  have hLnat : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.ne_of_gt hQ) (by omega))
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast hLnat
  have hL₀ : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hLone : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < L + 1)
  have hG : 0 < γ⁻¹ + 1 := by positivity
  have heps : 0 < 1 - γ := sub_pos.mpr hγ₁
  have hB : 0 < B := by
    dsimp [B]
    have hlog := Real.log_pos hLone
    have hpow := Real.rpow_pos_of_pos (lt_trans zero_lt_one hLone) (1 - γ)
    positivity
  have hCB : 0 ≤ C_B := by dsimp [C_B]; positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact div_nonneg (mul_nonneg hA (Real.rpow_nonneg hL₀.le _)) hL₀.le
  have hBpow : B ≤ C_B * (L : ℝ) ^ (2 * (1 - γ)) := by
    simpa only [B, C_B, Nat.cast_add, Nat.cast_one] using
      log_envelope_power_bound hG.le hL (sub_pos.mpr hγ₁)
  have hEpow : E ≤ A * (L : ℝ) ^ (-σ) :=
    (phase_error_normalization (L : ℝ) A σ hL₀).le
  have hw : ∀ n ∈ initialInterval (Q * M),
      ‖(discrepancyWeight γ (n + 1) : ℂ)‖ ≤ B := by
    intro n hn
    have hnL : n + 1 ≤ L + 1 :=
      Nat.add_le_add_right (Finset.mem_Icc.mp hn).2 1
    simpa only [Complex.norm_real, Real.norm_eq_abs, B] using
      discrepancyWeight_le_envelope hγ₀ hγ₁.le (by omega : 1 ≤ n + 1) hnL
  have hp : PhaseBound d M (fun y => (discrepancyWeight γ (Q * y + 1) : ℂ))
      (((Q * M : ℕ) : ℝ) * E) := by
    convert hphase using 1
    change (L : ℝ) * (A * (L : ℝ) ^ (1 - σ) / L) = A * (L : ℝ) ^ (1 - σ)
    field_simp
  have hraw := countingForm_comparison_finite N Q M d K hQ (by omega) P hP
    (fun n => (discrepancyWeight γ n : ℂ)) f₀ f C hVN B E hB hE hw hp
  have hfactor : (L : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹ ≤ (Q : ℝ) ^ 2 := by
    simpa only [div_eq_mul_inv] using (liftedScale_normalization_bounds N Q d hN hQ hd hM).2
  have hsave := weighted_root_modulus_saving hL (Nat.cast_nonneg Q) hB hE hCB hA
    (sub_nonneg.mpr hγ₁.le) ht₀.le ht₁ hs₁ hsσ hsmall hBpow hEpow hQpow
  have hcoeff : 0 ≤ C * (C_B + C_B ^ (1 - t) * A ^ t) := by positivity
  have heta : 0 ≤ s * t / 4 := by positivity
  calc
    _ ≤ ((L : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹) *
        (B * C * ((L : ℝ)⁻¹ + E / B) ^ t) := hraw
    _ = C * (((L : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹) *
        (B * ((L : ℝ)⁻¹ + E / B) ^ t)) := by ring
    _ ≤ C * ((Q : ℝ) ^ 2 * (B * ((L : ℝ)⁻¹ + E / B) ^ t)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfactor (by positivity)) hC
    _ ≤ C * ((C_B + C_B ^ (1 - t) * A ^ t) * (L : ℝ) ^ (-(s * t) / 4)) :=
      mul_le_mul_of_nonneg_left hsave hC
    _ = (C * (C_B + C_B ^ (1 - t) * A ^ t)) * (L : ℝ) ^ (-(s * t / 4)) := by
      rw [neg_div, mul_assoc]
    _ ≤ (C * (C_B + C_B ^ (1 - t) * A ^ t)) *
        ((2 : ℝ) ^ (s * t / 4) * (N : ℝ) ^ (-(s * t / 4) / (d : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (negative_rpow_liftedScale_le N Q d hN hQ hd hM (s * t / 4) heta) hcoeff
    _ = _ := by ring

end PSPrimes
