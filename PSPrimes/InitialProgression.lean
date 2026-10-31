import PSPrimes.RecurrenceDefinitions

/-!
# Exact arithmetic-progression initialization

Residues are represented in `[1-Q,0]`, as in the proof of Theorem 1.1.
The weighted pigeonhole argument uses full residue-class intersections,
so no boundary points are discarded before the density comparison.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- Weighted finite pigeonhole principle, in denominator-free form. -/
theorem exists_dense_fiber {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A U : Finset α) (f : α → β) (hA : A ⊆ U) (hU : U.Nonempty) :
    ∃ r ∈ U.image f,
      (A.card : ℝ) * ((U.filter (fun x => f x = r)).card : ℝ) ≤
        ((A.filter (fun x => f x = r)).card : ℝ) * (U.card : ℝ) := by
  classical
  have hsumU : (U.card : ℝ) = ∑ r ∈ U.image f,
      ((U.filter (fun x => f x = r)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (show (U : Set α).MapsTo f (U.image f) from fun x hx => Finset.mem_image_of_mem f hx)
  have hsumA : (A.card : ℝ) = ∑ r ∈ U.image f,
      ((A.filter (fun x => f x = r)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (show (A : Set α).MapsTo f (U.image f) from fun x hx => Finset.mem_image_of_mem f (hA hx))
  by_contra h
  push_neg at h
  have hlt := Finset.sum_lt_sum_of_nonempty (hU.image f) h
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← hsumU, ← hsumA] at hlt
  exact (lt_irrefl _) hlt

/-- The canonical representative in the manuscript's interval `[1-Q,0]`. -/
def initialResidueRepresentative (Q : ℕ) (x : ℤ) : ℤ :=
  (x - 1) % (Q : ℤ) + 1 - (Q : ℤ)

/-- The full length of the residue class, with its real floor explicit. -/
def initialResidueLength (N Q : ℕ) (r : ℤ) : ℕ :=
  ⌊((N : ℝ) - (r : ℝ)) / (Q : ℝ)⌋₊

/-- Actual pullback of `A` to the entire progression intersection. -/
def initialPullback (A : Finset ℤ) (N Q : ℕ) (r : ℤ) : Finset ℤ :=
  (integerInterval (initialResidueLength N Q r)).filter
    (fun u => r + (Q : ℤ) * u ∈ A)

theorem initialResidueRepresentative_bounds (Q : ℕ) (hQ : 0 < Q) (x : ℤ) :
    1 - (Q : ℤ) ≤ initialResidueRepresentative Q x ∧
      initialResidueRepresentative Q x ≤ 0 := by
  have hQint : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hnonneg := Int.emod_nonneg (x - 1) (ne_of_gt hQint)
  have hlt := Int.emod_lt_of_pos (x - 1) hQint
  unfold initialResidueRepresentative
  omega

theorem initialResidueRepresentative_dvd (Q : ℕ) (x : ℤ) :
    (Q : ℤ) ∣ x - initialResidueRepresentative Q x := by
  refine ⟨(x - 1) / (Q : ℤ) + 1, ?_⟩
  have h := Int.emod_add_ediv (x - 1) (Q : ℤ)
  unfold initialResidueRepresentative
  nlinarith

theorem initialResidueRepresentative_eq_iff (Q : ℕ) (hQ : 0 < Q) (x r : ℤ)
    (hrlo : 1 - (Q : ℤ) ≤ r) (hrhi : r ≤ 0) :
    initialResidueRepresentative Q x = r ↔ (Q : ℤ) ∣ x - r := by
  constructor
  · intro h
    simpa [h] using initialResidueRepresentative_dvd Q x
  · intro hdiv
    have hQint : (0 : ℤ) < Q := by exact_mod_cast hQ
    have hrmod : (r - 1) % (Q : ℤ) = r - 1 + (Q : ℤ) := by
      calc
        (r - 1) % (Q : ℤ) = (r - 1 + (Q : ℤ)) % (Q : ℤ) := by simp
        _ = r - 1 + (Q : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
    have hmod : (x - 1) % (Q : ℤ) = (r - 1) % (Q : ℤ) := by
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      apply Int.emod_eq_zero_of_dvd
      convert hdiv using 1
      ring
    unfold initialResidueRepresentative
    rw [hmod, hrmod]
    ring

/-- The full class has positive length when `Q ≤ N`. -/
theorem initialResidueLength_pos (N Q : ℕ) (hQ : 0 < Q) (hQN : Q ≤ N)
    (r : ℤ) (hr : r ≤ 0) : 1 ≤ initialResidueLength N Q r := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrreal : (r : ℝ) ≤ 0 := by exact_mod_cast hr
  have hQNreal : (Q : ℝ) ≤ N := by exact_mod_cast hQN
  have hbase : (1 : ℝ) ≤ ((N : ℝ) - r) / Q := by
    apply (le_div_iff₀ hQreal).mpr
    linarith
  apply (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ ((N : ℝ) - r) / Q)).mpr
  simpa using hbase

/-- The exact real floor bound used in `e:initial-scale`. -/
theorem initialResidueLength_lower (N Q : ℕ) (hQ : 0 < Q)
    (r : ℤ) (hr : r ≤ 0) :
    (N : ℝ) / (Q : ℝ) - 1 ≤ (initialResidueLength N Q r : ℝ) := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrreal : (r : ℝ) ≤ 0 := by exact_mod_cast hr
  have hbase : (N : ℝ) / Q ≤ ((N : ℝ) - r) / Q :=
    div_le_div_of_nonneg_right (by linarith) hQreal.le
  have hfloor := Nat.lt_floor_add_one (((N : ℝ) - r) / Q)
  change ((N : ℝ) - r) / Q < (initialResidueLength N Q r : ℝ) + 1 at hfloor
  linarith

/-- The convenient half-length consequence, with the necessary finite range. -/
theorem initialResidueLength_half_lower (N Q : ℕ) (hQ : 0 < Q)
    (hN : 2 * Q ≤ N) (r : ℤ) (hr : r ≤ 0) :
    (N : ℝ) / (2 * (Q : ℝ)) ≤ (initialResidueLength N Q r : ℝ) := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNreal : (2 : ℝ) * Q ≤ N := by exact_mod_cast hN
  have htwo : (2 : ℝ) ≤ (N : ℝ) / Q := (le_div_iff₀ hQreal).mpr hNreal
  have hfloor := initialResidueLength_lower N Q hQ r hr
  have hid : (N : ℝ) / (2 * (Q : ℝ)) = ((N : ℝ) / Q) / 2 := by ring
  rw [hid]
  linarith

/-- The whole interval intersection with one residue class is precisely the
arithmetic progression of the stated floor length. -/
theorem mem_initialProgression_iff (N Q : ℕ) (hQ : 0 < Q) (r x : ℤ)
    (hrlo : 1 - (Q : ℤ) ≤ r) (hrhi : r ≤ 0) :
    x ∈ arithmeticProgression r Q (initialResidueLength N Q r) ↔
      x ∈ integerInterval N ∧ (Q : ℤ) ∣ x - r := by
  have hQint : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrreal : (r : ℝ) ≤ 0 := by exact_mod_cast hrhi
  have hratio : (0 : ℝ) ≤ ((N : ℝ) - r) / Q :=
    div_nonneg (by linarith [show (0 : ℝ) ≤ N by positivity]) hQreal.le
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    simp only [integerInterval, Finset.mem_Icc] at hu
    have hureal : (u : ℝ) ≤ ((N : ℝ) - r) / Q := by
      have hule : (u : ℝ) ≤ (initialResidueLength N Q r : ℝ) := by exact_mod_cast hu.2
      exact hule.trans (Nat.floor_le hratio)
    have hmulR := (le_div_iff₀ hQreal).mp hureal
    have hmulZ : u * (Q : ℤ) ≤ (N : ℤ) - r := by exact_mod_cast hmulR
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨u, by ring⟩⟩
    · nlinarith [hu.1]
    · nlinarith
  · rintro ⟨hx, u, hu⟩
    simp only [integerInterval, Finset.mem_Icc] at hx
    have huone : 1 ≤ u := by nlinarith [hx.1]
    have hu0 : 0 ≤ u := by omega
    have hcastZ : (u.toNat : ℤ) = u := Int.toNat_of_nonneg hu0
    have hcastR : (u.toNat : ℝ) = (u : ℝ) := by exact_mod_cast hcastZ
    have hureal : (u.toNat : ℝ) ≤ ((N : ℝ) - r) / Q := by
      rw [hcastR]
      apply (le_div_iff₀ hQreal).mpr
      exact_mod_cast (show u * (Q : ℤ) ≤ (N : ℤ) - r by nlinarith [hx.2])
    have hnat : u.toNat ≤ initialResidueLength N Q r := (Nat.le_floor_iff hratio).mpr hureal
    have huint : u ≤ (initialResidueLength N Q r : ℤ) := by
      have huint' : (u.toNat : ℤ) ≤ (initialResidueLength N Q r : ℤ) := by exact_mod_cast hnat
      rwa [hcastZ] at huint'
    apply Finset.mem_image.mpr
    refine ⟨u, Finset.mem_Icc.mpr ⟨huone, huint⟩, ?_⟩
    linarith

/-- Full residue fibers, rather than truncated progressions, are used in the
weighted pigeonhole principle. -/
theorem initialProgression_eq_fiber (N Q : ℕ) (hQ : 0 < Q) (r : ℤ)
    (hrlo : 1 - (Q : ℤ) ≤ r) (hrhi : r ≤ 0) :
    arithmeticProgression r Q (initialResidueLength N Q r) =
      (integerInterval N).filter (fun x => initialResidueRepresentative Q x = r) := by
  ext x
  rw [mem_initialProgression_iff N Q hQ r x hrlo hrhi, Finset.mem_filter,
    initialResidueRepresentative_eq_iff Q hQ x r hrlo hrhi]

/-- The affine image of the actual pullback is exactly the chosen part of `A`. -/
theorem initialPullback_image (A : Finset ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (hA : A ⊆ integerInterval N) (r : ℤ)
    (hrlo : 1 - (Q : ℤ) ≤ r) (hrhi : r ≤ 0) :
    (initialPullback A N Q r).image (fun u => r + (Q : ℤ) * u) =
      A.filter (fun x => initialResidueRepresentative Q x = r) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨huI, huA⟩ := Finset.mem_filter.mp hu
    have hxAP : r + (Q : ℤ) * u ∈
        arithmeticProgression r Q (initialResidueLength N Q r) :=
      Finset.mem_image.mpr ⟨u, huI, rfl⟩
    have hdiv := (mem_initialProgression_iff N Q hQ r _ hrlo hrhi).mp hxAP
    exact Finset.mem_filter.mpr ⟨huA,
      (initialResidueRepresentative_eq_iff Q hQ _ r hrlo hrhi).mpr hdiv.2⟩
  · intro hx
    obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
    have hxAP : x ∈ arithmeticProgression r Q (initialResidueLength N Q r) :=
      (mem_initialProgression_iff N Q hQ r x hrlo hrhi).mpr
        ⟨hA hxA, (initialResidueRepresentative_eq_iff Q hQ x r hrlo hrhi).mp hxr⟩
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hxAP
    apply Finset.mem_image.mpr
    refine ⟨u, Finset.mem_filter.mpr ⟨hu, ?_⟩, hux⟩
    rwa [hux]

/-- No collisions occur in the affine pullback, so its cardinality is exact. -/
theorem card_initialPullback (A : Finset ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (hA : A ⊆ integerInterval N) (r : ℤ)
    (hrlo : 1 - (Q : ℤ) ≤ r) (hrhi : r ≤ 0) :
    (initialPullback A N Q r).card =
      (A.filter (fun x => initialResidueRepresentative Q x = r)).card := by
  have hinj : Function.Injective (fun u : ℤ => r + (Q : ℤ) * u) := by
    intro u v h
    exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hQ : (Q : ℤ) ≠ 0)
      (add_left_cancel h)
  calc
    (initialPullback A N Q r).card =
        ((initialPullback A N Q r).image (fun u => r + (Q : ℤ) * u)).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = (A.filter (fun x => initialResidueRepresentative Q x = r)).card := by
      rw [initialPullback_image A N Q hQ hA r hrlo hrhi]

/-- The actual initial residue progression has at least the original density.
This is weighted averaging over full residue intersections; no endpoint
truncation or equal-size-cell assumption is used. -/
theorem exists_initial_residue (A : Finset ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (hQN : Q ≤ N) (hA : A ⊆ integerInterval N) :
    ∃ r : ℤ, 1 - (Q : ℤ) ≤ r ∧ r ≤ 0 ∧
      1 ≤ initialResidueLength N Q r ∧
      initialPullback A N Q r ⊆ integerInterval (initialResidueLength N Q r) ∧
      (A.card : ℝ) / (N : ℝ) ≤
        ((initialPullback A N Q r).card : ℝ) / (initialResidueLength N Q r : ℝ) ∧
      (N : ℝ) / (Q : ℝ) - 1 ≤ (initialResidueLength N Q r : ℝ) := by
  have hN : 1 ≤ N := by omega
  obtain ⟨r, hr, hdense⟩ := exists_dense_fiber A (integerInterval N)
    (initialResidueRepresentative Q) hA (integerInterval_nonempty hN)
  obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp hr
  have hrange := initialResidueRepresentative_bounds Q hQ x
  rw [hxr] at hrange
  have hlength := initialResidueLength_pos N Q hQ hQN r hrange.2
  have hcellcard :
      ((integerInterval N).filter (fun x => initialResidueRepresentative Q x = r)).card =
        initialResidueLength N Q r := by
    rw [← initialProgression_eq_fiber N Q hQ r hrange.1 hrange.2]
    exact card_arithmeticProgression r Q _ hQ
  have hAcard := card_initialPullback A N Q hQ hA r hrange.1 hrange.2
  rw [hcellcard, ← hAcard, card_integerInterval] at hdense
  refine ⟨r, hrange.1, hrange.2, hlength, Finset.filter_subset _ _, ?_,
    initialResidueLength_lower N Q hQ r hrange.2⟩
  apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < N))
    (by exact_mod_cast (by omega : 0 < initialResidueLength N Q r))).mpr
  exact hdense

end PSPrimes
