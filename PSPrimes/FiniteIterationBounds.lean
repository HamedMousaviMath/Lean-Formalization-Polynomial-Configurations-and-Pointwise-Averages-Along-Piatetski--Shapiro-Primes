import PSPrimes.RecurrenceIteration
import PSPrimes.SmoothModuli

/-!
# Finite bounds from the actual logarithmic density recurrences

The constants and exponents in this module are chosen before α, the horizon,
or the sequences of stage lengths and moduli. This derives the finite estimates
needed by `uniform_iteration_admissibility` from the one-step recurrences.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace PSPrimes

theorem inverse_log_add_one_le {α : ℝ} (hα : 0 < α) :
    Real.log α⁻¹ + 1 ≤ α⁻¹ := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hα)
  linarith

theorem reciprocal_density_power_mono {α E A : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1) (hEA : E ≤ A) :
    α ^ (-E) ≤ α ^ (-A) :=
  Real.rpow_le_rpow_of_exponent_ge hα hα₁ (by linarith)

theorem log_times_density_power_le {α E : ℝ} (hα : 0 < α) :
    (Real.log α⁻¹ + 1) * α ^ (-E) ≤ α ^ (-(E + 1)) := by
  calc
    _ ≤ α⁻¹ * α ^ (-E) := mul_le_mul_of_nonneg_right (inverse_log_add_one_le hα)
      (Real.rpow_nonneg hα.le _)
    _ = _ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hα]
      congr 1
      ring

theorem inverse_log_product_le {α : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) :
    (Real.log α⁻¹ + 1) * Real.log α⁻¹ ≤ α ^ (-(2 : ℝ)) := by
  have hlog : 0 ≤ Real.log α⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hα.le hα₁)
  have hlogle : Real.log α⁻¹ ≤ α⁻¹ := by linarith [inverse_log_add_one_le hα]
  calc
    _ ≤ α⁻¹ * α⁻¹ := mul_le_mul (inverse_log_add_one_le hα) hlogle hlog (inv_nonneg.mpr hα.le)
    _ = _ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hα]
      norm_num

/-- Finite-horizon modulus and length control with no asymptotic estimates
among the hypotheses. The one-step length recurrence is precisely the form
obtained by taking logarithms of the progression length lower bound.
The final exponent A also dominates the initial exponent A₀. -/
theorem finite_iteration_bounds (θ B C J A₀ H₀ Hq₀ : ℝ)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hH₀ : 0 ≤ H₀) (hHq₀ : 0 ≤ Hq₀) :
    ∃ A : ℝ, 0 < A ∧ A₀ ≤ A ∧
      ∃ b : ℝ, 0 < b ∧ ∃ Hlen : ℝ, 0 ≤ Hlen ∧
        ∃ Clen : ℝ, 0 ≤ Clen ∧ ∃ Hq : ℝ, 0 ≤ Hq ∧
          ∀ (α X : ℝ) (L q : ℕ → ℝ) (H n : ℕ),
            0 < α → α ≤ 1 → 0 ≤ X →
            (H : ℝ) ≤ J * (Real.log α⁻¹ + 1) →
            0 ≤ q 0 → q 0 ≤ Hq₀ * α ^ (-A₀) →
            X - H₀ * α ^ (-A₀) ≤ L 0 →
            (∀ j < H, q (j + 1) ≤ B * q j) →
            (∀ j < H, L j ≤ X) →
            (∀ j < H, θ * L j - C * (q j + Real.log α⁻¹ + Real.sqrt (L j)) ≤ L (j + 1)) →
            n ≤ H →
            q n ≤ Hq * α ^ (-A) ∧
              b * α ^ A * X - Hlen * α ^ (-A) -
                Clen * (Real.log α⁻¹ + 1) * Real.sqrt X ≤ L n := by
  let E_B : ℝ := J * Real.log B
  let Eθ : ℝ := -(J * Real.log θ)
  let E : ℝ := E_B + A₀
  let A : ℝ := max 2 (max Eθ (E + 1))
  let b : ℝ := Real.exp (J * Real.log θ)
  let Hq : ℝ := Real.exp (J * Real.log B) * Hq₀
  let Hlen : ℝ := H₀ + J * C * (Hq + 1)
  let Clen : ℝ := J * C
  have hEB : 0 ≤ E_B := mul_nonneg hJ (Real.log_nonneg hB)
  have hA₂ : (2 : ℝ) ≤ A := le_max_left _ _
  have hEA : E + 1 ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hEθA : Eθ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by dsimp [E] at hEA; linarith only [hEA, hEB]
  have hb : 0 < b := Real.exp_pos _
  have hHq : 0 ≤ Hq := mul_nonneg (Real.exp_pos _).le hHq₀
  have hHlen : 0 ≤ Hlen := by dsimp [Hlen]; positivity
  have hClen : 0 ≤ Clen := mul_nonneg hJ hC
  refine ⟨A, by linarith, hA₀A, b, hb, Hlen, hHlen, Clen, hClen, Hq, hHq, ?_⟩
  intro α X L q H n hα hα₁ hX hH hq₀ hq₀upper hL₀ hqstep hLupper hLstep hn
  have hlog : 0 ≤ Real.log α⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hα.le hα₁)
  have hBH : B ^ H * q 0 ≤ Hq * α ^ (-E) := by
    have hgrowth := horizon_growth_bound hα hB H hH
    calc
      _ ≤ (Real.exp (J * Real.log B) * α ^ (-E_B)) *
          (Hq₀ * α ^ (-A₀)) :=
        mul_le_mul hgrowth hq₀upper hq₀ (by positivity)
      _ = _ := by
        dsimp [Hq, E]
        rw [show -(E_B + A₀) = -E_B + -A₀ by ring, Real.rpow_add hα]
        ring
  have hquniform : ∀ j ≤ H, q j ≤ Hq * α ^ (-E) := by
    intro j hj
    calc
      q j ≤ B ^ j * q 0 := modulus_upper_of_recurrence q (by linarith) hqstep hj
      _ ≤ B ^ H * q 0 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hj) hq₀
      _ ≤ _ := hBH
  have hqfinal : q n ≤ Hq * α ^ (-A) :=
    (hquniform n hn).trans (mul_le_mul_of_nonneg_left
      (reciprocal_density_power_mono hα hα₁ (by linarith : E ≤ A)) hHq)
  let Err : ℝ := C * (Hq * α ^ (-E) + Real.log α⁻¹ + Real.sqrt X)
  have hErr : 0 ≤ Err := by dsimp [Err]; positivity
  have hstep : ∀ j < H, θ * L j - Err ≤ L (j + 1) := by
    intro j hj
    have hqj := hquniform j (by omega)
    have hsqrt := Real.sqrt_le_sqrt (hLupper j hj)
    have herror : C * (q j + Real.log α⁻¹ + Real.sqrt (L j)) ≤ Err := by
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    linarith only [herror, hLstep j hj]
  have hfinite := length_lower_of_uniform_error_coarse L hθ.le hθ₁ hErr hstep hn
  have hnH : (n : ℝ) ≤ J * (Real.log α⁻¹ + 1) :=
    (by exact_mod_cast hn : (n : ℝ) ≤ H).trans hH
  have hθn := horizon_contraction_lower hα hθ hθ₁ n hnH
  have hleading : b * α ^ A ≤ θ ^ n := by
    apply le_trans _ hθn
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hα hα₁ hEθA) hb.le
  have hinitloss : θ ^ n * (H₀ * α ^ (-A₀)) ≤ H₀ * α ^ (-A) := by
    calc
      _ ≤ 1 * (H₀ * α ^ (-A₀)) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ₁) (by positivity)
      _ ≤ _ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (reciprocal_density_power_mono hα hα₁ hA₀A) hH₀
  have hinitmul := mul_le_mul_of_nonneg_left hL₀ (pow_nonneg hθ.le n)
  have hleadX := mul_le_mul_of_nonneg_right hleading hX
  have hleadfinal : b * α ^ A * X - H₀ * α ^ (-A) ≤ θ ^ n * L 0 := by
    nlinarith only [hinitmul, hleadX, hinitloss]
  have hlogpower : (Real.log α⁻¹ + 1) * α ^ (-E) ≤ α ^ (-A) :=
    (log_times_density_power_le hα).trans (reciprocal_density_power_mono hα hα₁ hEA)
  have hlogproduct : (Real.log α⁻¹ + 1) * Real.log α⁻¹ ≤ α ^ (-A) :=
    (inverse_log_product_le hα hα₁).trans (reciprocal_density_power_mono hα hα₁ hA₂)
  have hErrbound : Err * (J * (Real.log α⁻¹ + 1)) ≤
      (J * C * (Hq + 1)) * α ^ (-A) +
        (J * C) * (Real.log α⁻¹ + 1) * Real.sqrt X := by
    calc
      _ = (J * C * Hq) * ((Real.log α⁻¹ + 1) * α ^ (-E)) +
          (J * C) * ((Real.log α⁻¹ + 1) * Real.log α⁻¹) +
          (J * C) * (Real.log α⁻¹ + 1) * Real.sqrt X := by dsimp [Err]; ring
      _ ≤ (J * C * Hq) * α ^ (-A) + (J * C) * α ^ (-A) +
          (J * C) * (Real.log α⁻¹ + 1) * Real.sqrt X := by
        apply add_le_add_right
        exact add_le_add
          (mul_le_mul_of_nonneg_left hlogpower (by positivity))
          (mul_le_mul_of_nonneg_left hlogproduct (by positivity))
      _ = _ := by ring
  have hErrn := (mul_le_mul_of_nonneg_left hnH hErr).trans hErrbound
  refine ⟨hqfinal, ?_⟩
  dsimp [Hlen, Clen]
  nlinarith only [hfinite, hErrn, hleadfinal]

/-- All numerical admissibility conditions hold at every finite prefix within
the logarithmic density horizon. The hypotheses are the actual initial and
one-step logarithmic bounds; no accumulated length estimate or admissibility
conclusion is assumed. The threshold precedes α, H, n and both stage sequences.
This theorem does not assume or assert that density-increment stages exist. -/
theorem quantitative_prefix_admissibility (θ B C J A₀ H₀ Hq₀ Hs c₀ ν : ℝ)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hH₀ : 0 ≤ H₀) (hHq₀ : 0 ≤ Hq₀)
    (hHs : 0 ≤ Hs) (hc₀ : 0 < c₀) (hν : 0 < ν) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (α δ : ℝ) (sizes moduli : ℕ → ℕ) (s H n : ℕ),
        0 < α → α ≤ 1 → (Real.log (N : ℝ)) ^ (-κ) ≤ α → α ≤ δ →
        (s : ℝ) ≤ Hs * α ^ (-A₀) →
        (H : ℝ) ≤ J * (Real.log α⁻¹ + 1) →
        (∀ j ≤ H, 1 ≤ moduli j) →
        Real.log (moduli 0 : ℝ) ≤ Hq₀ * α ^ (-A₀) →
        Real.log (N : ℝ) - H₀ * α ^ (-A₀) ≤ Real.log (sizes 0 : ℝ) →
        (∀ j < H, Real.log (moduli (j + 1) : ℝ) ≤ B * Real.log (moduli j : ℝ)) →
        (∀ j < H, Real.log (sizes j : ℝ) ≤ Real.log (N : ℝ)) →
        (∀ j < H, θ * Real.log (sizes j : ℝ) -
          C * (Real.log (moduli j : ℝ) + Real.log α⁻¹ + Real.sqrt (Real.log (sizes j : ℝ))) ≤
            Real.log (sizes (j + 1) : ℝ)) →
        n ≤ H →
        (Real.log (N : ℝ)) ^ (3 / 4 : ℝ) ≤ Real.log (sizes n : ℝ) ∧
          (moduli n : ℝ) ≤ Real.exp ((Real.log (sizes n : ℝ)) ^ (2 * c₀)) ∧
          (s : ℝ) ≤ (Real.log (sizes n : ℝ)) ^ c₀ ∧
          (Real.log (sizes n : ℝ)) ^ (-ν) < δ := by
  obtain ⟨A, hA, hA₀A, b, hb, Hlen, hHlen, Clen, hClen, Hq, hHq, hfinite⟩ :=
    finite_iteration_bounds θ B C J A₀ H₀ Hq₀ hθ hθ₁ hB hC hJ hH₀ hHq₀
  obtain ⟨κ, hκ, hadmissible⟩ :=
    uniform_iteration_admissibility hA hb hHlen hClen hHq hHs hc₀ hν
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hadmissible] with N hN
  intro α δ sizes moduli s H n hα hα₁ hthreshold hαδ hs hH hmoduli hq₀ hL₀ hqstep hLupper hLstep hn
  have hq₀nonneg : 0 ≤ Real.log (moduli 0 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hmoduli 0 (Nat.zero_le H))
  have hbnd := hfinite α (Real.log (N : ℝ))
    (fun j => Real.log (sizes j : ℝ)) (fun j => Real.log (moduli j : ℝ)) H n
    hα hα₁ (Real.log_natCast_nonneg N) hH hq₀nonneg hq₀ hL₀ hqstep hLupper hLstep hn
  have hs' : (s : ℝ) ≤ Hs * α ^ (-A) := hs.trans
    (mul_le_mul_of_nonneg_left (reciprocal_density_power_mono hα hα₁ hA₀A) hHs)
  exact hN α δ (sizes n) (moduli n) s (hmoduli n hn) hthreshold hαδ hbnd.1 hs' hbnd.2

/-- The exact ceiling used to choose the fixed smoothness parameter. -/
theorem initial_smoothness_upper {α K C : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    (⌈K * α ^ (-C)⌉₊ : ℝ) ≤ (K + 1) * α ^ (-C) := by
  have hpow : 1 ≤ α ^ (-C) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hα hα₁ (by linarith)
  calc
    _ ≤ K * α ^ (-C) + 1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ K * α ^ (-C))).le
    _ ≤ _ := by nlinarith only [hpow]

theorem initial_smoothness_lower {α K C : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hK : 2 ≤ K) (hC : 0 ≤ C) :
    2 ≤ ⌈K * α ^ (-C)⌉₊ := by
  have hpow : 1 ≤ α ^ (-C) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hα hα₁ (by linarith)
  have hbase : (2 : ℝ) ≤ K * α ^ (-C) := by nlinarith
  simpa using Nat.ceil_le_ceil hbase

/-- As the density increases, its lower required smoothness decreases. -/
theorem smoothness_requirement_mono {α δ K C : ℝ} (hα : 0 < α) (hαδ : α ≤ δ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ⌈K * δ ^ (-C)⌉₊ ≤ ⌈K * α ^ (-C)⌉₊ := by
  apply Nat.ceil_le_ceil
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hα hαδ (by linarith)) hK

/-- The logarithm of the initial least common multiple is polynomial in the
reciprocal density, with an explicit exponent and constant. -/
theorem initial_modulus_log_bound {α K C : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    Real.log (smoothModulus ⌈K * α ^ (-C)⌉₊ : ℝ) ≤
      (K + 1) ^ 2 * α ^ (-(2 * C)) := by
  let s : ℕ := ⌈K * α ^ (-C)⌉₊
  have hs : (s : ℝ) ≤ (K + 1) * α ^ (-C) := initial_smoothness_upper hα hα₁ hK hC
  have hpow : (α ^ (-C)) ^ 2 = α ^ (-(2 * C)) := by
    rw [← Real.rpow_mul_natCast hα.le]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (s : ℝ) * Real.log (s : ℝ) := log_smoothModulus_le s
    _ ≤ (s : ℝ) * (s : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg s)) (Nat.cast_nonneg s)
    _ ≤ ((K + 1) * α ^ (-C)) ^ 2 := by
      simpa only [pow_two] using pow_le_pow_left₀ (Nat.cast_nonneg s) hs 2
    _ = _ := by rw [mul_pow, hpow]

/-- The same exponent can be used for initial smoothness and log modulus. -/
theorem initial_smoothness_upper_common_exponent {α K C : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    (⌈K * α ^ (-C)⌉₊ : ℝ) ≤ (K + 1) * α ^ (-(2 * C)) := by
  apply (initial_smoothness_upper hα hα₁ hK hC).trans
  exact mul_le_mul_of_nonneg_left
    (reciprocal_density_power_mono hα hα₁ (by linarith : C ≤ 2 * C)) (by linarith)

/-- The half-length initialization yields the initial logarithmic lower bound
required by the finite iteration, with all constants retained. -/
theorem initial_log_length_bound {N n Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (hsize : (N : ℝ) / (2 * (Q : ℝ)) ≤ (n : ℝ))
    {α A Hq : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hA : 0 ≤ A)
    (hq : Real.log (Q : ℝ) ≤ Hq * α ^ (-A)) :
    Real.log (N : ℝ) - (Real.log 2 + Hq) * α ^ (-A) ≤ Real.log (n : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hhalf : 0 < (N : ℝ) / (2 * (Q : ℝ)) := by positivity
  have hlog := Real.log_le_log hhalf hsize
  rw [Real.log_div hNreal.ne' (by positivity), Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQreal.ne'] at hlog
  have hpow : 1 ≤ α ^ (-A) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hα hα₁ (by linarith)
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have htwo' := mul_le_mul_of_nonneg_left hpow htwo
  nlinarith only [hlog, hq, htwo']

/-- A polynomial log-modulus bound is eventually small enough for the
half-length initialization. Its threshold precedes α and Q. -/
theorem eventually_initial_modulus_half {A Hq κ : ℝ}
    (hA : 0 ≤ A) (hHq : 0 ≤ Hq) (hκA : κ * A ≤ 1 / 8) :
    ∀ᶠ N : ℕ in atTop, ∀ (α : ℝ) (Q : ℕ),
      (Real.log (N : ℝ)) ^ (-κ) ≤ α → 1 ≤ Q →
      Real.log (Q : ℝ) ≤ Hq * α ^ (-A) → 2 * Q ≤ N := by
  have hlogt : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 8)).comp hlogt).eventually_ge_atTop
    (Hq + Real.log 2)
  filter_upwards [ht, hlogt.eventually_gt_atTop 1, eventually_ge_atTop 1]
    with N hlarge hX hN
  intro α Q hα hQ hq
  let X : ℝ := Real.log (N : ℝ)
  have hX₀ : 0 < X := lt_trans zero_lt_one hX
  have hnegpow : α ^ (-A) ≤ X ^ (1 / 8 : ℝ) :=
    reciprocal_density_power_le hX.le hα hA hκA
  have hq' : Real.log (Q : ℝ) ≤ Hq * X ^ (1 / 8 : ℝ) :=
    hq.trans (mul_le_mul_of_nonneg_left hnegpow hHq)
  have hone : 1 ≤ X ^ (1 / 8 : ℝ) := Real.one_le_rpow hX.le (by norm_num)
  have htwo := mul_le_mul_of_nonneg_left hone (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have hupper := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hX₀.le (1 / 8 : ℝ))
  have hid : X ^ (7 / 8 : ℝ) * X ^ (1 / 8 : ℝ) = X := by
    rw [← Real.rpow_add hX₀]
    norm_num
  change (Hq + Real.log 2) * X ^ (1 / 8 : ℝ) ≤ X ^ (7 / 8 : ℝ) * X ^ (1 / 8 : ℝ) at hupper
  rw [hid] at hupper
  have hlogsum : Real.log 2 + Real.log (Q : ℝ) ≤ X := by nlinarith only [hq', htwo, hupper]
  have hQ₀ : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogs : Real.log (2 * (Q : ℝ)) ≤ Real.log (N : ℝ) := by
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQ₀.ne']
  have hreal := (Real.log_le_log_iff (by positivity : (0 : ℝ) < 2 * (Q : ℝ)) hN₀).mp hlogs
  exact_mod_cast hreal

/-- The precise finite horizon from the manuscript, with the logarithmic
upper bound needed by the quantitative prefix argument. -/
theorem density_horizon_bounds {α β : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 1 < β) :
    let H : ℕ := ⌊Real.log α⁻¹ / Real.log β⌋₊ + 1
    (H : ℝ) ≤ (1 / Real.log β + 1) * (Real.log α⁻¹ + 1) ∧ 1 < β ^ H * α := by
  let H : ℕ := ⌊Real.log α⁻¹ / Real.log β⌋₊ + 1
  have hlogα : 0 ≤ Real.log α⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hα.le hα₁)
  have hlogβ : 0 < Real.log β := Real.log_pos hβ
  have hratio : 0 ≤ Real.log α⁻¹ / Real.log β := div_nonneg hlogα hlogβ.le
  have hfloor := Nat.floor_le hratio
  have hfloorlt : Real.log α⁻¹ / Real.log β < (H : ℝ) := by
    simpa only [H, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Real.log α⁻¹ / Real.log β)
  constructor
  · change (H : ℝ) ≤ _
    have hcast : (H : ℝ) = (⌊Real.log α⁻¹ / Real.log β⌋₊ : ℝ) + 1 := by simp [H]
    rw [hcast]
    have hinv : 0 ≤ (Real.log β)⁻¹ := inv_nonneg.mpr hlogβ.le
    simp only [div_eq_mul_inv, one_mul] at hfloor ⊢
    nlinarith only [hfloor, hlogα, hinv]
  · have hpowerlog : Real.log α⁻¹ < Real.log (β ^ H) := by
      rw [Real.log_pow]
      exact (div_lt_iff₀ hlogβ).mp hfloorlt
    have hβ₀ : 0 < β := lt_trans zero_lt_one hβ
    have hpower : α⁻¹ < β ^ H :=
      (Real.log_lt_log_iff (inv_pos.mpr hα) (pow_pos hβ₀ H)).mp hpowerlog
    exact (div_lt_iff₀ hα).mp (by simpa only [one_div] using hpower)

end PSPrimes
