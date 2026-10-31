import Mathlib

/-!
# Initialization and invariants of the smooth modulus

The initialization is the actual least common multiple of `[1,s]` from
Theorem 1.1. Prime support and divisibility are preserved under the positive
powers appearing in the iteration. No existence of density increments is
assumed or established in this file.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- All prime factors of `Q` are at most the fixed smoothness parameter `s`. -/
def SmoothUpTo (s Q : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ s

/-- The manuscript's initialization `𝓛(s) = lcm(1,...,s)`. -/
def smoothModulus (s : ℕ) : ℕ := (Finset.Icc 1 s).lcm id

/-- Every positive integer at most `s` divides the initialization. -/
theorem dvd_smoothModulus {s k : ℕ} (hk : 1 ≤ k) (hks : k ≤ s) :
    k ∣ smoothModulus s := by
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hk, hks⟩)

/-- The initialized modulus divides `s!`, with no missing small-`s` case. -/
theorem smoothModulus_dvd_factorial (s : ℕ) : smoothModulus s ∣ s.factorial := by
  apply Finset.lcm_dvd
  intro k hk
  obtain ⟨hkpos, hks⟩ := Finset.mem_Icc.mp hk
  change k ∣ s.factorial
  exact Nat.dvd_factorial (by omega) hks

theorem smoothModulus_pos (s : ℕ) : 0 < smoothModulus s := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hfac := smoothModulus_dvd_factorial s
  rw [hzero, zero_dvd_iff] at hfac
  exact Nat.factorial_ne_zero s hfac

theorem smoothModulus_le_factorial (s : ℕ) : smoothModulus s ≤ s.factorial :=
  Nat.le_of_dvd (Nat.factorial_pos s) (smoothModulus_dvd_factorial s)

/-- The exact initialization is `s`-smooth, expressed without a largest-prime
factor convention for `Q=1`. -/
theorem smoothModulus_smooth (s : ℕ) : SmoothUpTo s (smoothModulus s) := by
  intro p hp hdiv
  exact hp.dvd_factorial.mp (hdiv.trans (smoothModulus_dvd_factorial s))

/-- The elementary logarithmic bound used before the first density increment. -/
theorem log_smoothModulus_le (s : ℕ) :
    Real.log (smoothModulus s : ℝ) ≤ (s : ℝ) * Real.log (s : ℝ) := by
  have hpow : (smoothModulus s : ℝ) ≤ (s : ℝ) ^ s := by
    exact_mod_cast (smoothModulus_le_factorial s).trans (Nat.factorial_le_pow s)
  calc
    Real.log (smoothModulus s : ℝ) ≤ Real.log ((s : ℝ) ^ s) :=
      Real.log_le_log (by exact_mod_cast smoothModulus_pos s) hpow
    _ = (s : ℝ) * Real.log (s : ℝ) := Real.log_pow _ _

/-- Taking any natural-number power introduces no new prime factors. -/
theorem SmoothUpTo.pow {s Q : ℕ} (hQ : SmoothUpTo s Q) (k : ℕ) :
    SmoothUpTo s (Q ^ k) := by
  intro p hp hpQ
  exact hQ p hp (hp.dvd_of_dvd_pow hpQ)

/-- Divisibility by the initialized modulus persists under positive powers. -/
theorem smoothModulus_dvd_pow {s Q k : ℕ} (hdiv : smoothModulus s ∣ Q)
    (hk : 1 ≤ k) : smoothModulus s ∣ Q ^ k := by
  exact hdiv.trans (dvd_pow_self Q (by omega : k ≠ 0))

/-- Joint invariant for one actual update `Q ↦ Q^(b+1)`. -/
theorem smooth_modulus_update {s Q : ℕ} (hQ : SmoothUpTo s Q)
    (hdiv : smoothModulus s ∣ Q) (b : ℕ) :
    SmoothUpTo s (Q ^ (b + 1)) ∧ smoothModulus s ∣ Q ^ (b + 1) :=
  ⟨hQ.pow (b + 1), smoothModulus_dvd_pow hdiv (by omega)⟩

end PSPrimes
