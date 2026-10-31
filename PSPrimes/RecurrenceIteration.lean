import PSPrimes.Iteration
import PSPrimes.Asymptotics

/-!
# Uniform admissibility for the density iteration

The threshold in each eventual statement is chosen before the initial density
and before any stage of the iteration. The finite logarithmic length estimate
is retained as a hypothesis until it is derived from the actual recurrence.
No density increment or admissibility conclusion is assumed as an input.
-/

noncomputable section
open Filter Topology

namespace PSPrimes

/-- A fixed positive leading coefficient still dominates both smaller powers.
The chosen threshold is independent of any density parameter. -/
theorem eventually_power_gap {b D : ℝ} (hb : 0 < b) (hD : 0 ≤ D) :
    ∀ᶠ X : ℝ in atTop,
      X ^ (3 / 4 : ℝ) ≤ b * X ^ (7 / 8 : ℝ) - D * X ^ (5 / 8 : ℝ) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop
    (max 1 ((D + 2) / b))
  filter_upwards [ht, eventually_ge_atTop 1] with X hlarge hX
  have hX₀ : 0 < X := lt_of_lt_of_le zero_lt_one hX
  let u : ℝ := X ^ (1 / 8 : ℝ)
  have hu₁ : 1 ≤ u := (le_max_left _ _).trans hlarge
  have hbu : D + 2 ≤ b * u := by
    have h := (le_max_right 1 ((D + 2) / b)).trans hlarge
    exact (div_le_iff₀ hb).mp h |>.trans_eq (by ring)
  have hmul := mul_le_mul_of_nonneg_right hbu (show 0 ≤ u by linarith)
  have hDu : D ≤ D * u := by nlinarith
  have hquad : u ≤ b * u ^ 2 - D := by nlinarith
  have h78 : X ^ (7 / 8 : ℝ) = X ^ (5 / 8 : ℝ) * u ^ 2 := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast hX₀.le, ← Real.rpow_add hX₀]
    norm_num
  have h34 : X ^ (3 / 4 : ℝ) = X ^ (5 / 8 : ℝ) * u := by
    dsimp [u]
    rw [← Real.rpow_add hX₀]
    norm_num
  calc
    _ = X ^ (5 / 8 : ℝ) * u := h34
    _ ≤ X ^ (5 / 8 : ℝ) * (b * u ^ 2 - D) :=
      mul_le_mul_of_nonneg_left hquad (Real.rpow_nonneg hX₀.le _)
    _ = _ := by rw [h78]; ring

/-- The density threshold controls the reciprocal powers of the initial
density uniformly. This is used for moduli, smoothness and error terms. -/
theorem reciprocal_density_power_le {X α κ A p : ℝ}
    (hX : 1 ≤ X) (hα : X ^ (-κ) ≤ α) (hA : 0 ≤ A) (hκA : κ * A ≤ p) :
    α ^ (-A) ≤ X ^ p := by
  have hX₀ : 0 < X := lt_of_lt_of_le zero_lt_one hX
  calc
    _ ≤ (X ^ (-κ)) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hX₀ _) hα (by linarith)
    _ = X ^ (κ * A) := by rw [← Real.rpow_mul hX₀.le]; congr 1; ring
    _ ≤ X ^ p := Real.rpow_le_rpow_of_exponent_le hX hκA

/-- The manuscript's logarithmic length lower estimate implies a fixed power
of the original logarithmic length. All constants are explicit and independent
of α, Y and the iteration index. This theorem does not derive the finite lower
estimate from the progression length recurrence. -/
theorem uniform_log_length_lower {A b H C κ : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hκA : κ * A ≤ 1 / 8) :
    ∀ᶠ X : ℝ in atTop, ∀ α Y : ℝ, X ^ (-κ) ≤ α →
      b * α ^ A * X - H * α ^ (-A) -
        C * (Real.log α⁻¹ + 1) * Real.sqrt X ≤ Y →
      X ^ (3 / 4 : ℝ) ≤ Y := by
  let D : ℝ := H + C * (1 / A + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [eventually_power_gap hb hD, eventually_ge_atTop 1]
    with X hgap hX
  intro α Y hα hlength
  have hX₀ : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hα₀ : 0 < α := (Real.rpow_pos_of_pos hX₀ _).trans_le hα
  have hnegpow : α ^ (-A) ≤ X ^ (1 / 8 : ℝ) :=
    reciprocal_density_power_le hX hα hA.le hκA
  have hαpow : X ^ (-(1 / 8 : ℝ)) ≤ α ^ A := by
    calc
      _ ≤ X ^ ((-κ) * A) :=
        Real.rpow_le_rpow_of_exponent_le hX (by nlinarith)
      _ = (X ^ (-κ)) ^ A := Real.rpow_mul hX₀.le _ _
      _ ≤ α ^ A := Real.rpow_le_rpow (Real.rpow_nonneg hX₀.le _) hα hA.le
  have hpow : X ^ (-(1 / 8 : ℝ)) * X = X ^ (7 / 8 : ℝ) := by
    simpa only [Real.rpow_one, show -(1 / 8 : ℝ) + 1 = 7 / 8 by norm_num]
      using (Real.rpow_add hX₀ (-(1 / 8 : ℝ)) 1).symm
  have hlead : X ^ (7 / 8 : ℝ) ≤ α ^ A * X := by
    have h := mul_le_mul_of_nonneg_right hαpow hX₀.le
    rwa [hpow] at h
  have hlog : Real.log α⁻¹ ≤ α ^ (-A) / A := by
    calc
      _ ≤ (α⁻¹) ^ A / A := Real.log_le_rpow_div (inv_nonneg.mpr hα₀.le) hA
      _ = α ^ (-A) / A := by rw [Real.inv_rpow hα₀.le, Real.rpow_neg hα₀.le]
  have hlog' : Real.log α⁻¹ ≤ X ^ (1 / 8 : ℝ) / A :=
    hlog.trans (div_le_div_of_nonneg_right hnegpow hA.le)
  have hone : (1 : ℝ) ≤ X ^ (1 / 8 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hlogone : Real.log α⁻¹ + 1 ≤ (1 / A + 1) * X ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ X ^ (1 / 8 : ℝ) / A + X ^ (1 / 8 : ℝ) := add_le_add hlog' hone
      _ = _ := by ring
  have hsqrt : X ^ (1 / 8 : ℝ) * Real.sqrt X = X ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX₀]
    norm_num
  have herr : C * (Real.log α⁻¹ + 1) * Real.sqrt X ≤
      (C * (1 / A + 1)) * X ^ (5 / 8 : ℝ) := by
    calc
      _ ≤ C * ((1 / A + 1) * X ^ (1 / 8 : ℝ)) * Real.sqrt X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogone hC)
          (Real.sqrt_nonneg X)
      _ = _ := by rw [mul_assoc C, mul_assoc (1 / A + 1), hsqrt]; ring
  have herrH : H * α ^ (-A) ≤ H * X ^ (5 / 8 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hH
    exact hnegpow.trans (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  have hleadb := mul_le_mul_of_nonneg_left hlead hb.le
  dsimp [D] at hgap
  nlinarith

/-- Uniform admissibility from the finite bounds on log length, log modulus
and smoothness. `q` denotes log Q and `S` denotes the fixed smoothness parameter.
No admissibility conclusion appears among the hypotheses. -/
theorem uniform_density_admissibility_fixed {A b H C Hq Hs κ c₀ ν : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hHq : 0 ≤ Hq) (hHs : 0 ≤ Hs) (hc₀ : 0 < c₀) (hν : 0 < ν)
    (hκA₁ : κ * A ≤ 1 / 8) (hκA₂ : κ * A ≤ c₀ / 4)
    (hκν : κ < 3 * ν / 4) :
    ∀ᶠ X : ℝ in atTop, ∀ α δ Y q S : ℝ,
      X ^ (-κ) ≤ α → α ≤ δ → q ≤ Hq * α ^ (-A) → S ≤ Hs * α ^ (-A) →
      b * α ^ A * X - H * α ^ (-A) -
        C * (Real.log α⁻¹ + 1) * Real.sqrt X ≤ Y →
      X ^ (3 / 4 : ℝ) ≤ Y ∧ q ≤ Y ^ (2 * c₀) ∧ S ≤ Y ^ c₀ ∧ Y ^ (-ν) < δ := by
  have ht := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < c₀ / 4)).eventually_ge_atTop
    (max Hq Hs)
  filter_upwards [uniform_log_length_lower hA hb hH hC hκA₁, ht,
    eventually_gt_atTop 1] with X hlength hlarge hX
  intro α δ Y q S hα hαδ hq hS hlen
  have hX₀ : 0 < X := lt_trans zero_lt_one hX
  have hY := hlength α Y hα hlen
  have hYone : 1 ≤ Y := (Real.one_le_rpow hX.le (by norm_num : (0 : ℝ) ≤ 3 / 4)).trans hY
  have hαpow : α ^ (-A) ≤ X ^ (c₀ / 4) :=
    reciprocal_density_power_le hX.le hα hA.le hκA₂
  have hpowmul : X ^ (c₀ / 4) * X ^ (c₀ / 4) = X ^ (c₀ / 2) := by
    rw [← Real.rpow_add hX₀]
    congr 1
    ring
  have hq' : q ≤ X ^ (c₀ / 2) := by
    calc
      _ ≤ Hq * α ^ (-A) := hq
      _ ≤ Hq * X ^ (c₀ / 4) := mul_le_mul_of_nonneg_left hαpow hHq
      _ ≤ X ^ (c₀ / 4) * X ^ (c₀ / 4) :=
        mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hlarge) (Real.rpow_nonneg hX₀.le _)
      _ = _ := hpowmul
  have hS' : S ≤ X ^ (c₀ / 2) := by
    calc
      _ ≤ Hs * α ^ (-A) := hS
      _ ≤ Hs * X ^ (c₀ / 4) := mul_le_mul_of_nonneg_left hαpow hHs
      _ ≤ X ^ (c₀ / 4) * X ^ (c₀ / 4) :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hlarge) (Real.rpow_nonneg hX₀.le _)
      _ = _ := hpowmul
  have hscale : X ^ (c₀ / 2) ≤ Y ^ c₀ := by
    calc
      _ ≤ X ^ ((3 / 4 : ℝ) * c₀) :=
        Real.rpow_le_rpow_of_exponent_le hX.le (by nlinarith)
      _ = (X ^ (3 / 4 : ℝ)) ^ c₀ := Real.rpow_mul hX₀.le _ _
      _ ≤ Y ^ c₀ := Real.rpow_le_rpow (Real.rpow_nonneg hX₀.le _) hY hc₀.le
  have hqfinal : q ≤ Y ^ (2 * c₀) :=
    (hq'.trans hscale).trans (Real.rpow_le_rpow_of_exponent_le hYone (by linarith))
  have hYneg : Y ^ (-ν) ≤ X ^ (-(3 / 4 : ℝ) * ν) := by
    calc
      _ ≤ (X ^ (3 / 4 : ℝ)) ^ (-ν) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hX₀ _) hY (by linarith)
      _ = _ := by rw [← Real.rpow_mul hX₀.le]; congr 1; ring
  have hstrict : X ^ (-(3 / 4 : ℝ) * ν) < X ^ (-κ) :=
    Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
  exact ⟨hY, hqfinal, hS'.trans hscale, (hYneg.trans_lt hstrict).trans_le (hα.trans hαδ)⟩

/-- There is one positive density exponent and one threshold before all
densities and stages. The coefficients in the finite bookkeeping bounds may
depend on the fixed polynomial family, as in the manuscript. -/
theorem uniform_density_admissibility {A b H C Hq Hs c₀ ν : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hHq : 0 ≤ Hq) (hHs : 0 ≤ Hs) (hc₀ : 0 < c₀) (hν : 0 < ν) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ X : ℝ in atTop, ∀ α δ Y q S : ℝ,
      X ^ (-κ) ≤ α → α ≤ δ → q ≤ Hq * α ^ (-A) → S ≤ Hs * α ^ (-A) →
      b * α ^ A * X - H * α ^ (-A) -
        C * (Real.log α⁻¹ + 1) * Real.sqrt X ≤ Y →
      X ^ (3 / 4 : ℝ) ≤ Y ∧ q ≤ Y ^ (2 * c₀) ∧ S ≤ Y ^ c₀ ∧ Y ^ (-ν) < δ := by
  let κ : ℝ := min (1 / (8 * A)) (min (c₀ / (4 * A)) (ν / 2))
  have hκ : 0 < κ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hκA₁ : κ * A ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_right (min_le_left (1 / (8 * A))
      (min (c₀ / (4 * A)) (ν / 2))) hA.le
    change κ * A ≤ (1 / (8 * A)) * A at h
    have heq : (1 / (8 * A)) * A = 1 / 8 := by
      field_simp
      ring
    exact h.trans_eq heq
  have hκA₂ : κ * A ≤ c₀ / 4 := by
    have hκle : κ ≤ c₀ / (4 * A) := (min_le_right _ _).trans (min_le_left _ _)
    have h := mul_le_mul_of_nonneg_right hκle hA.le
    have heq : (c₀ / (4 * A)) * A = c₀ / 4 := by
      field_simp
      ring
    exact h.trans_eq heq
  have hκν : κ < 3 * ν / 4 := by
    have hκle : κ ≤ ν / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  exact ⟨κ, hκ, uniform_density_admissibility_fixed hA hb hH hC hHq hHs hc₀ hν
    hκA₁ hκA₂ hκν⟩

/-- The numerical admissibility conditions in the manuscript's variables.
The eventual threshold in N precedes α and all stage data. Smoothness and
divisibility invariants are algebraic obligations handled separately. -/
theorem uniform_iteration_admissibility {A b H C Hq Hs c₀ ν : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hHq : 0 ≤ Hq) (hHs : 0 ≤ Hs) (hc₀ : 0 < c₀) (hν : 0 < ν) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop, ∀ (α δ : ℝ) (n Q s : ℕ),
      1 ≤ Q → (Real.log (N : ℝ)) ^ (-κ) ≤ α → α ≤ δ →
      Real.log (Q : ℝ) ≤ Hq * α ^ (-A) → (s : ℝ) ≤ Hs * α ^ (-A) →
      b * α ^ A * Real.log (N : ℝ) - H * α ^ (-A) -
        C * (Real.log α⁻¹ + 1) * Real.sqrt (Real.log (N : ℝ)) ≤ Real.log (n : ℝ) →
      (Real.log (N : ℝ)) ^ (3 / 4 : ℝ) ≤ Real.log (n : ℝ) ∧
        (Q : ℝ) ≤ Real.exp ((Real.log (n : ℝ)) ^ (2 * c₀)) ∧
        (s : ℝ) ≤ (Real.log (n : ℝ)) ^ c₀ ∧ (Real.log (n : ℝ)) ^ (-ν) < δ := by
  obtain ⟨κ, hκ, hadmissible⟩ := uniform_density_admissibility hA hb hH hC hHq hHs hc₀ hν
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [ht.eventually hadmissible] with N hN
  intro α δ n Q s hQ hα hαδ hq hs hlen
  obtain ⟨hY, hqY, hsY, hδY⟩ := hN α δ (Real.log (n : ℝ)) (Real.log (Q : ℝ))
    (s : ℝ) hα hαδ hq hs hlen
  refine ⟨hY, ?_, hsY, hδY⟩
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  rw [← Real.exp_log hQreal]
  exact Real.exp_le_exp.mpr hqY

/-- A logarithmic bound on the number of steps turns geometric modulus
growth into a power of the reciprocal initial density, with its exact constant. -/
theorem horizon_growth_bound {α B J : ℝ} (hα : 0 < α) (hB : 1 ≤ B) (H : ℕ)
    (hH : (H : ℝ) ≤ J * (Real.log α⁻¹ + 1)) :
    B ^ H ≤ Real.exp (J * Real.log B) * α ^ (-(J * Real.log B)) := by
  have hB₀ : 0 < B := lt_of_lt_of_le zero_lt_one hB
  calc
    _ = Real.exp ((H : ℝ) * Real.log B) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hB₀ H)]
    _ ≤ Real.exp ((J * (Real.log α⁻¹ + 1)) * Real.log B) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hH (Real.log_nonneg hB))
    _ = _ := by
      rw [Real.rpow_def_of_pos hα, ← Real.exp_add, Real.log_inv]
      congr 1
      ring

/-- The same finite horizon retains a power of the initial density in the
leading length term. Here θ is the actual degree ratio r/d, in (0,1]. -/
theorem horizon_contraction_lower {α θ J : ℝ} (hα : 0 < α) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) (H : ℕ) (hH : (H : ℝ) ≤ J * (Real.log α⁻¹ + 1)) :
    Real.exp (J * Real.log θ) * α ^ (-(J * Real.log θ)) ≤ θ ^ H := by
  have hlog : Real.log θ ≤ 0 := Real.log_nonpos hθ.le hθ₁
  calc
    _ = Real.exp ((J * (Real.log α⁻¹ + 1)) * Real.log θ) := by
      rw [Real.rpow_def_of_pos hα, ← Real.exp_add, Real.log_inv]
      congr 1
      ring
    _ ≤ Real.exp ((H : ℝ) * Real.log θ) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hH hlog)
    _ = θ ^ H := by rw [← Real.log_pow, Real.exp_log (pow_pos hθ H)]

end PSPrimes
