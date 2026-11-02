import Mathlib

/-!
# Summing power savings on arbitrary lacunary sequences

The first sample is at least one.  Consequently all constants below are
independent of that sample and of the particular lacunary sequence.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- A positive integer sequence growing by a factor at least `rho > 1`
dominates the geometric sequence starting at one. -/
theorem lacunary_geometric_lower_bound {rho : ℝ} (hrho : 1 < rho)
    (N : ℕ → ℕ) (hN : 1 ≤ N 0)
    (hstep : ∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) :
    ∀ j, rho ^ j ≤ (N j : ℝ) := by
  intro j
  induction j with
  | zero => simpa using (show (1 : ℝ) ≤ N 0 by exact_mod_cast hN)
  | succ j ih =>
    calc
      rho ^ (j + 1) = rho * rho ^ j := pow_succ' _ _
      _ ≤ rho * (N j : ℝ) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ (N (j + 1) : ℝ) := hstep j

theorem lacunary_positive {rho : ℝ} (hrho : 1 < rho)
    (N : ℕ → ℕ) (hN : 1 ≤ N 0)
    (hstep : ∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) :
    ∀ j, 1 ≤ N j := by
  intro j
  have h := lacunary_geometric_lower_bound hrho N hN hstep j
  have hpow : (0 : ℝ) < rho ^ j := pow_pos (by linarith) _
  have : (0 : ℝ) < N j := hpow.trans_le h
  have : 0 < N j := by exact_mod_cast this
  omega

/-- A decaying power along any positive `rho`-lacunary sequence is bounded
termwise by a geometric sequence with ratio `rho ^ (-η) < 1`. -/
theorem lacunary_rpow_le_geometric {rho η : ℝ} (hrho : 1 < rho) (hη : 0 < η)
    (N : ℕ → ℕ) (hN : 1 ≤ N 0)
    (hstep : ∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) (j : ℕ) :
    (N j : ℝ) ^ (-η) ≤ (rho ^ (-η)) ^ j := by
  have hlow := lacunary_geometric_lower_bound hrho N hN hstep j
  have hrhopos : 0 < rho := by linarith
  calc
    (N j : ℝ) ^ (-η) ≤ (rho ^ j) ^ (-η) :=
      Real.rpow_le_rpow_of_nonpos (pow_pos hrhopos _) hlow (by linarith)
    _ = (rho ^ (-η)) ^ j := by
      rw [← Real.rpow_natCast_mul hrhopos.le, mul_comm, Real.rpow_mul_natCast hrhopos.le]

/-- The full infinite summability estimate used in Corollary 4.2.  The
constant depends only on the saving and lacunarity, not on the sequence. -/
theorem lacunary_rpow_summable_le {rho η : ℝ} (hrho : 1 < rho) (hη : 0 < η)
    (N : ℕ → ℕ) (hN : 1 ≤ N 0)
    (hstep : ∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) :
    Summable (fun j => (N j : ℝ) ^ (-η)) ∧
      (∑' j, (N j : ℝ) ^ (-η)) ≤ (1 - rho ^ (-η))⁻¹ := by
  have hratio₀ : 0 ≤ rho ^ (-η) := Real.rpow_nonneg (by linarith) _
  have hratio₁ : rho ^ (-η) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hrho (by linarith)
  have hgeom := summable_geometric_of_lt_one hratio₀ hratio₁
  have hbound := lacunary_rpow_le_geometric hrho hη N hN hstep
  have hsum : Summable (fun j => (N j : ℝ) ^ (-η)) :=
    Summable.of_nonneg_of_le (fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _) hbound hgeom
  refine ⟨hsum, ?_⟩
  calc
    (∑' j, (N j : ℝ) ^ (-η)) ≤ ∑' j : ℕ, (rho ^ (-η)) ^ j :=
      hsum.tsum_le_tsum hbound hgeom
    _ = (1 - rho ^ (-η))⁻¹ := tsum_geometric_of_lt_one hratio₀ hratio₁

/-- Extended-nonnegative-real form, so an infinite variation or integral
cannot be hidden by the real-valued infinite-sum convention. -/
theorem lacunary_rpow_tsum_ennreal_le {rho η : ℝ} (hrho : 1 < rho) (hη : 0 < η)
    (N : ℕ → ℕ) (hN : 1 ≤ N 0)
    (hstep : ∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) :
    (∑' j, ENNReal.ofReal ((N j : ℝ) ^ (-η))) ≤
      ENNReal.ofReal ((1 - rho ^ (-η))⁻¹) := by
  obtain ⟨hsum, hb⟩ := lacunary_rpow_summable_le hrho hη N hN hstep
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum]
  exact ENNReal.ofReal_le_ofReal hb

end PSPrimes
