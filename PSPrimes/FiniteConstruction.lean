import Mathlib

namespace PSPrimes

/-- Finite dependent construction. The extension hypothesis is checked on
the already constructed prefix, so it does not assume a future infinite
chain or the existence of all admissible recurrence stages. -/
theorem finite_chain_of_extendable_prefix {S : Type*} (initial : S)
    (R : S → S → Prop) (H : ℕ)
    (hstep : ∀ n < H, ∀ s : ℕ → S, s 0 = initial →
      (∀ j < n, R (s j) (s (j + 1))) → ∃ t, R (s n) t) :
    ∃ s : ℕ → S, s 0 = initial ∧ ∀ j < H, R (s j) (s (j + 1)) := by
  suffices ∀ n : ℕ, n ≤ H → ∃ s : ℕ → S,
      s 0 = initial ∧ ∀ j < n, R (s j) (s (j + 1)) from this H le_rfl
  intro n
  induction n with
  | zero =>
    intro hn
    exact ⟨fun _ => initial, rfl, by intro j hj; omega⟩
  | succ n ih =>
    intro hn
    obtain ⟨s, hs₀, hs⟩ := ih (by omega)
    obtain ⟨t, ht⟩ := hstep n (by omega) s hs₀ hs
    let g : ℕ → S := fun i => if i ≤ n then s i else t
    refine ⟨g, by simpa [g] using hs₀, ?_⟩
    intro j hj
    by_cases hjn : j < n
    · simpa only [g, if_pos (by omega : j ≤ n), if_pos (by omega : j + 1 ≤ n)] using hs j hjn
    · have hjeq : j = n := by omega
      subst j
      simpa only [g, if_pos le_rfl, if_neg (by omega : ¬n + 1 ≤ n)] using ht

end PSPrimes
