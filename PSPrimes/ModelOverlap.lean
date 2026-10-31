import PSPrimes.Definitions

noncomputable section
open scoped BigOperators

namespace PSPrimes

def translatedIntervalIntersection {k : ℕ} (N : ℕ) (a : Fin k → ℤ) : Finset ℤ :=
  (Finset.Icc 1 (N : ℤ)).filter (fun x => ∀ i, x + a i ∈ Finset.Icc 1 (N : ℤ))

/-- The geometric overlap used in (26), with the manuscript's constants.
No sign restriction on the shifts is imposed. -/
theorem card_translatedIntervalIntersection_ge_half {k : ℕ}
    (N : ℕ) (hN : 0 < N) (a : Fin k → ℤ)
    (ha : ∀ i, |(a i : ℝ)| ≤ (N : ℝ) / 10) :
    (N : ℝ) / 2 ≤ ((translatedIntervalIntersection N a).card : ℝ) := by
  classical
  let m : ℤ := (N : ℤ) / 5
  let center : Finset ℤ := Finset.Icc (m + 1) ((N : ℤ) - m)
  have hNint : (0 : ℤ) < N := by exact_mod_cast hN
  have hm : 0 ≤ m := Int.ediv_nonneg (by positivity) (by norm_num)
  have haInt (i : Fin k) : |a i| ≤ m := by
    have hreal : (10 : ℝ) * |(a i : ℝ)| ≤ (N : ℝ) := by linarith [ha i]
    have hint : (10 : ℤ) * |a i| ≤ (N : ℤ) := by exact_mod_cast hreal
    dsimp [m]
    omega
  have hsub : center ⊆ translatedIntervalIntersection N a := by
    intro x hx
    have hx' := Finset.mem_Icc.mp hx
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i
      have hai := abs_le.mp (haInt i)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : (center.card : ℤ) = (N : ℤ) - 2 * m := by
    simp only [center, Int.card_Icc]
    rw [Int.toNat_of_nonneg (by dsimp [m]; omega)]
    ring
  have hcardR : (center.card : ℝ) = (N : ℝ) - 2 * (m : ℝ) := by
    exact_mod_cast hcard
  have hmupper : (5 : ℤ) * m ≤ (N : ℤ) := by dsimp [m]; omega
  have hmupperR : (5 : ℝ) * (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmupper
  have hbound : (N : ℝ) / 2 ≤ (center.card : ℝ) := by
    rw [hcardR]
    have : (0 : ℝ) ≤ N := by positivity
    linarith
  exact hbound.trans (by exact_mod_cast Finset.card_le_card hsub)

end PSPrimes
