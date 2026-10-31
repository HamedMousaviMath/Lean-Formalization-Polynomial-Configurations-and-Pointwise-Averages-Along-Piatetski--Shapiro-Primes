import Mathlib

/-!
# Exact finite bookkeeping for the density iteration

This module proves finite recurrence bounds used by the manuscript labels
`e:modulus-control`, `e:length-recursion`, and `e:length-control`. The variables `q j` and `L j` represent `log Q_j` and `log N_j`.
It does not assert that density increments exist or that their hypotheses
remain admissible. In particular, the asymptotic choice of the initial
density exponent and the uniform admissibility bridge remain separate.
-/

namespace PSPrimes

open scoped BigOperators

/-- Error accumulated through `n` applications of an affine lower recurrence.
The `k`th error is multiplied by `θ^(n-1-k)`. -/
def iterationError (θ : ℝ) (E : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, θ ^ (n - 1 - k) * E k

@[simp] theorem iterationError_zero (θ : ℝ) (E : ℕ → ℝ) :
    iterationError θ E 0 = 0 := by simp [iterationError]

/-- The finite sum has exactly the recurrence dictated by iteration. -/
theorem iterationError_succ (θ : ℝ) (E : ℕ → ℝ) (n : ℕ) :
    iterationError θ E (n + 1) = θ * iterationError θ E n + E n := by
  unfold iterationError
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hexp : n - k = (n - 1 - k) + 1 := by omega
  rw [hexp, pow_succ]
  ring

/-- Exact finite lower bound, retaining every individual error. -/
theorem length_lower_of_recurrence (L E : ℕ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    {H n : ℕ} (hstep : ∀ j < H, θ * L j - E j ≤ L (j + 1))
    (hn : n ≤ H) :
    θ ^ n * L 0 - iterationError θ E n ≤ L n := by
  revert hn
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hprev := ih (by omega : n ≤ H)
    calc
      θ ^ (n + 1) * L 0 - iterationError θ E (n + 1) =
          θ * (θ ^ n * L 0 - iterationError θ E n) - E n := by
        rw [iterationError_succ, pow_succ]
        ring
      _ ≤ θ * L n - E n :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hprev hθ) _
      _ ≤ L (n + 1) := hstep n (by omega)

/-- A uniform bound on the individual errors gives the usual geometric sum. -/
theorem iterationError_le_geometric {θ Emax : ℝ} (hθ : 0 ≤ θ)
    (E : ℕ → ℝ) (n : ℕ) (hE : ∀ k < n, E k ≤ Emax) :
    iterationError θ E n ≤ Emax * ∑ k ∈ Finset.range n, θ ^ k := by
  calc
    iterationError θ E n ≤
        ∑ k ∈ Finset.range n, θ ^ (n - 1 - k) * Emax := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hE k (Finset.mem_range.mp hk))
        (pow_nonneg hθ _)
    _ = (∑ k ∈ Finset.range n, θ ^ (n - 1 - k)) * Emax := by
      rw [Finset.sum_mul]
    _ = Emax * ∑ k ∈ Finset.range n, θ ^ k := by
      rw [Finset.sum_range_reflect]
      ring

/-- Constant-error corollary, including the endpoint cases `θ = 0` and `θ = 1`.
No division by `1-θ` is used. -/
theorem length_lower_of_uniform_error (L : ℕ → ℝ) {θ Emax : ℝ}
    (hθ : 0 ≤ θ) {H n : ℕ}
    (hstep : ∀ j < H, θ * L j - Emax ≤ L (j + 1)) (hn : n ≤ H) :
    θ ^ n * L 0 - Emax * (∑ k ∈ Finset.range n, θ ^ k) ≤ L n := by
  have hexact := length_lower_of_recurrence L (fun _ ↦ Emax) hθ hstep hn
  have herr := iterationError_le_geometric (Emax := Emax) hθ (fun _ ↦ Emax) n (by simp)
  linarith

/-- For a contraction, the total constant error is at most `n * Emax`.
This is the coarse finite estimate underlying the manuscript's accumulated
`log(α⁻¹) * sqrt(log N)` loss. -/
theorem length_lower_of_uniform_error_coarse (L : ℕ → ℝ) {θ Emax : ℝ}
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hE : 0 ≤ Emax) {H n : ℕ}
    (hstep : ∀ j < H, θ * L j - Emax ≤ L (j + 1)) (hn : n ≤ H) :
    θ ^ n * L 0 - Emax * (n : ℝ) ≤ L n := by
  have hsum : (∑ k ∈ Finset.range n, θ ^ k) ≤ (n : ℝ) := by
    calc
      (∑ k ∈ Finset.range n, θ ^ k) ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact pow_le_one₀ hθ hθone
      _ = (n : ℝ) := by simp
  have hbound := length_lower_of_uniform_error L hθ hstep hn
  have herr := mul_le_mul_of_nonneg_left hsum hE
  linarith

/-- Finite geometric control of the logarithm of the modulus. -/
theorem modulus_upper_of_recurrence (q : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    {H n : ℕ} (hstep : ∀ j < H, q (j + 1) ≤ B * q j) (hn : n ≤ H) :
    q n ≤ B ^ n * q 0 := by
  revert hn
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    calc
      q (n + 1) ≤ B * q n := hstep n (by omega)
      _ ≤ B * (B ^ n * q 0) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) hB
      _ = B ^ (n + 1) * q 0 := by rw [pow_succ]; ring

/-- Direct logarithmic specialization for the actual modulus power update.
The exponent `b j` here is the manuscript's `b_j+1`. -/
theorem log_modulus_upper_of_power_update (Q : ℕ → ℝ) (b : ℕ → ℕ)
    {B : ℝ} (hB : 0 ≤ B) {H n : ℕ}
    (hQ : ∀ j ≤ H, 1 ≤ Q j)
    (hupdate : ∀ j < H, Q (j + 1) = Q j ^ b j)
    (hb : ∀ j < H, (b j : ℝ) ≤ B) (hn : n ≤ H) :
    Real.log (Q n) ≤ B ^ n * Real.log (Q 0) := by
  apply modulus_upper_of_recurrence (fun j ↦ Real.log (Q j)) hB (n := n) (H := H)
    _ hn
  intro j hj
  change Real.log (Q (j + 1)) ≤ B * Real.log (Q j)
  rw [hupdate j hj, Real.log_pow]
  exact mul_le_mul_of_nonneg_right (hb j hj) (Real.log_nonneg (hQ j (by omega)))

/-- Uniform finite-horizon bookkeeping for the manuscript's length recurrence.
The explicit error bound uses geometric modulus growth and an upper bound
on log length. Deriving a sufficiently long admissible horizon from the
paper's density threshold is not included in this theorem. -/
theorem length_lower_finite_horizon (L q : ℕ → ℝ) {θ B C A U : ℝ}
    (hθ : 0 ≤ θ) (hB : 1 ≤ B) (hC : 0 ≤ C) (hq0 : 0 ≤ q 0)
    {H n : ℕ} (hqstep : ∀ j < H, q (j + 1) ≤ B * q j)
    (hLupper : ∀ j < H, L j ≤ U)
    (hLstep : ∀ j < H,
      θ * L j - C * (q j + A + Real.sqrt (L j)) ≤ L (j + 1))
    (hn : n ≤ H) :
    θ ^ n * L 0 -
      (C * (B ^ H * q 0 + A + Real.sqrt U)) *
        (∑ k ∈ Finset.range n, θ ^ k) ≤ L n := by
  apply length_lower_of_uniform_error L hθ (H := H) _ hn
  intro j hj
  have hqj : q j ≤ B ^ j * q 0 :=
    modulus_upper_of_recurrence q (by linarith) hqstep (by omega : j ≤ H)
  have hpow : B ^ j ≤ B ^ H := pow_le_pow_right₀ hB (by omega)
  have hquniform : q j ≤ B ^ H * q 0 :=
    hqj.trans (mul_le_mul_of_nonneg_right hpow hq0)
  have hsqrt : Real.sqrt (L j) ≤ Real.sqrt U := Real.sqrt_le_sqrt (hLupper j hj)
  have herr : C * (q j + A + Real.sqrt (L j)) ≤
      C * (B ^ H * q 0 + A + Real.sqrt U) := by
    apply mul_le_mul_of_nonneg_left _ hC
    linarith
  linarith [hLstep j hj]

end PSPrimes
