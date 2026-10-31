import Mathlib

noncomputable section
open Filter Topology

namespace PSPrimes

/-- The precise eventual absorption behind Q = N^{o(1)}.
The threshold may depend on a and ε; the bound has multiplicative constant 1. -/
theorem exp_log_subpower_le_rpow {a ε : ℝ} (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.exp ((Real.log x) ^ a) ≤ x ^ ε := by
  have ht : Tendsto (fun x : ℝ => (Real.log x) ^ (-(1 - a))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - a)).comp
      Real.tendsto_log_atTop
  have he : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (-(1 - a)) < ε :=
    (tendsto_order.mp ht).2 ε hε
  filter_upwards [he, eventually_gt_atTop 1] with x hx hx₁
  have hx₀ : 0 < x := lt_trans zero_lt_one hx₁
  have hlog : 0 < Real.log x := Real.log_pos hx₁
  have hid : (Real.log x) ^ (-(1 - a)) * Real.log x = (Real.log x) ^ a := by
    calc
      _ = (Real.log x) ^ (-(1 - a)) * (Real.log x) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log x) ^ (-(1 - a) + 1) := (Real.rpow_add hlog _ _).symm
      _ = (Real.log x) ^ a := by congr 1; ring
  have hmul := mul_le_mul_of_nonneg_right hx.le hlog.le
  rw [hid] at hmul
  rw [Real.rpow_def_of_pos hx₀]
  exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hmul)

/-- A modulus bounded by exp((log N)^a) is eventually bounded by N^ε,
uniformly over every modulus in that range. -/
theorem modulus_subpower {a ε : ℝ} (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
      (Q : ℝ) ≤ (N : ℝ) ^ ε := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
    (exp_log_subpower_le_rpow ha hε)
  filter_upwards [h] with N hN
  intro Q hQ
  exact hQ.trans hN

end PSPrimes
