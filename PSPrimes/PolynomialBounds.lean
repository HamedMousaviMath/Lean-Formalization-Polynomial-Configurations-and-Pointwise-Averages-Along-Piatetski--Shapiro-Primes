import PSPrimes.Rescaling
import PSPrimes.Scales

/-!
# Uniform bounds for rescaled polynomial shifts

Coefficientwise integer rescaling has no constant term, even before imposing
that hypothesis on the original polynomial. The bounds below apply to the
actual integer polynomial `rescale P q`, with no external mathematical input.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace PSPrimes

/-- Uniform finite coefficient bound, retaining one factor of the parameter.
The original polynomial may have a constant term because `rescale` discards it. -/
theorem abs_eval_rescale_le (P : Polynomial ℤ) (q y : ℤ) (M C : ℝ) (d : ℕ)
    (hq : 1 ≤ q) (hM : 1 ≤ M) (hy : 0 ≤ y) (hyM : (y : ℝ) ≤ M)
    (hC : 0 ≤ C) (hdeg : P.natDegree ≤ d)
    (hcoeff : ∀ j ≤ d, |(P.coeff j : ℝ)| ≤ C) :
    |(((rescale P q).eval y : ℤ) : ℝ)| ≤
      C * (d + 1 : ℕ) * (q : ℝ) ^ (d - 1) * (y : ℝ) * M ^ (d - 1) := by
  classical
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hyr : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hq0 : (0 : ℝ) ≤ q := le_trans zero_le_one hqr
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have heval : (((rescale P q).eval y : ℤ) : ℝ) =
      ∑ j ∈ Finset.range (d + 1), ((rescale P q).coeff j : ℝ) * (y : ℝ) ^ j := by
    rw [Polynomial.eval_eq_sum_range'
      (lt_of_le_of_lt (le_trans (natDegree_rescale_le P q) hdeg) (Nat.lt_succ_self d))]
    push_cast
    rfl
  have hterm (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
      |((rescale P q).coeff j : ℝ) * (y : ℝ) ^ j| ≤
        C * (q : ℝ) ^ (d - 1) * (y : ℝ) * M ^ (d - 1) := by
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hj0 : j = 0
    · subst j
      simp only [coeff_rescale_zero, Int.cast_zero, zero_mul, abs_zero]
      positivity
    have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hqp : (q : ℝ) ^ (j - 1) ≤ (q : ℝ) ^ (d - 1) :=
      pow_le_pow_right₀ hqr (Nat.sub_le_sub_right hjd 1)
    have hyp : (y : ℝ) ^ j ≤ (y : ℝ) * M ^ (d - 1) := by
      calc
        (y : ℝ) ^ j = (y : ℝ) * (y : ℝ) ^ (j - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        _ ≤ (y : ℝ) * M ^ (j - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hyr hyM _) hyr
        _ ≤ (y : ℝ) * M ^ (d - 1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hM (Nat.sub_le_sub_right hjd 1)) hyr
    rw [coeff_rescale, if_neg hj0]
    push_cast
    rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hq0,
      abs_of_nonneg hyr]
    calc
      |(P.coeff j : ℝ)| * (q : ℝ) ^ (j - 1) * (y : ℝ) ^ j ≤
          C * (q : ℝ) ^ (d - 1) * ((y : ℝ) * M ^ (d - 1)) := by
        exact mul_le_mul (mul_le_mul (hcoeff j hjd) hqp (by positivity) hC)
          hyp (by positivity) (by positivity)
      _ = C * (q : ℝ) ^ (d - 1) * (y : ℝ) * M ^ (d - 1) := by ring
  calc
    |(((rescale P q).eval y : ℤ) : ℝ)| =
        |∑ j ∈ Finset.range (d + 1),
          ((rescale P q).coeff j : ℝ) * (y : ℝ) ^ j| := by rw [heval]
    _ ≤ ∑ j ∈ Finset.range (d + 1),
        |((rescale P q).coeff j : ℝ) * (y : ℝ) ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (d + 1),
        C * (q : ℝ) ^ (d - 1) * (y : ℝ) * M ^ (d - 1) :=
      Finset.sum_le_sum hterm
    _ = C * (d + 1 : ℕ) * (q : ℝ) ^ (d - 1) * (y : ℝ) * M ^ (d - 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- A fixed short initial segment makes every rescaled shift at most `N/10`.
This finite statement isolates the geometric argument from taking a floor. -/
theorem abs_eval_rescale_le_tenth_of_scale (P : Polynomial ℤ) (q y : ℤ)
    (M C N : ℝ) (d : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M) (hy : 0 ≤ y)
    (hd : 1 ≤ d) (hC : 1 ≤ C) (hdeg : P.natDegree ≤ d)
    (hcoeff : ∀ j ≤ d, |(P.coeff j : ℝ)| ≤ C)
    (hscale : (q : ℝ) ^ (d - 1) * M ^ d ≤ N)
    (hshort : (y : ℝ) ≤ M / (10 * C * (d + 1 : ℕ))) :
    |(((rescale P q).eval y : ℤ) : ℝ)| ≤ N / 10 := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hdcast : (1 : ℝ) ≤ (d + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ d + 1)
  have hden : (0 : ℝ) < 10 * C * (d + 1 : ℕ) := by positivity
  have hprod : C * (d + 1 : ℕ) * (y : ℝ) ≤ M / 10 := by
    have h := (le_div_iff₀ hden).mp hshort
    nlinarith
  have hyM : (y : ℝ) ≤ M := by
    have hynonneg : (0 : ℝ) ≤ y := by exact_mod_cast hy
    have hcprod : 1 ≤ C * (d + 1 : ℕ) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hcprod hynonneg
    nlinarith
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast (by omega : 0 ≤ q)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hpow : M ^ (d - 1) * M = M ^ d := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    |(((rescale P q).eval y : ℤ) : ℝ)| ≤
        C * (d + 1 : ℕ) * (q : ℝ) ^ (d - 1) * (y : ℝ) * M ^ (d - 1) :=
      abs_eval_rescale_le P q y M C d hq hM hy hyM hC0 hdeg hcoeff
    _ = ((q : ℝ) ^ (d - 1) * M ^ (d - 1)) *
        (C * (d + 1 : ℕ) * (y : ℝ)) := by ring
    _ ≤ ((q : ℝ) ^ (d - 1) * M ^ (d - 1)) * (M / 10) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((q : ℝ) ^ (d - 1) * M ^ d) / 10 := by rw [← hpow]; ring
    _ ≤ N / 10 := by linarith [hscale]

/-- The initial fraction `1/(10*C*(d+1))` works uniformly in the modulus
for the actual floor scale of the manuscript. -/
theorem abs_eval_rescale_le_tenth_floorScale (P : Polynomial ℤ) (Q N d : ℕ)
    (y : ℤ) (C : ℝ) (hQ : 1 ≤ Q) (hd : 1 ≤ d)
    (hM : 1 ≤ floorScale N Q d) (hy : 0 ≤ y) (hC : 1 ≤ C)
    (hdeg : P.natDegree ≤ d) (hcoeff : ∀ j ≤ d, |(P.coeff j : ℝ)| ≤ C)
    (hshort : (y : ℝ) ≤ (1 / (10 * C * (d + 1 : ℕ))) * floorScale N Q d) :
    |(((rescale P (Q : ℤ)).eval y : ℤ) : ℝ)| ≤ (N : ℝ) / 10 := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hscale : (Q : ℝ) ^ (d - 1) * (floorScale N Q d : ℝ) ^ d ≤ N := by
    have h := (floorScale_power_bounds N Q d (by omega) hM).1
    have hh := (le_div_iff₀ (pow_pos hQreal (d - 1))).mp h
    simpa only [mul_comm] using hh
  apply abs_eval_rescale_le_tenth_of_scale P (Q : ℤ) y
    (floorScale N Q d) C N d (by exact_mod_cast hQ) (by exact_mod_cast hM)
    hy hd hC hdeg hcoeff
  · simpa using hscale
  · simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hshort

end PSPrimes
