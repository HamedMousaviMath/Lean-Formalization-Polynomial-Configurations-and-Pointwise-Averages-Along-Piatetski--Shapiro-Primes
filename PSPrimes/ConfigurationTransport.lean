import PSPrimes.PrimeDiscrepancy

noncomputable section
namespace PSPrimes

def affinePullback (A : Finset ℤ) (a : ℤ) (K L : ℕ) : Finset ℤ :=
  (integerInterval L).filter (fun u => a + (K : ℤ) * u ∈ A)

theorem affinePullback_subset (A : Finset ℤ) (a : ℤ) (K L : ℕ) :
    affinePullback A a K L ⊆ integerInterval L := Finset.filter_subset _ _

theorem affinePullback_image (A : Finset ℤ) (a : ℤ) (K L : ℕ) :
    (affinePullback A a K L).image (fun u => a + (K : ℤ) * u) =
      A ∩ arithmeticProgression a K L := by
  classical
  ext x
  simp only [affinePullback, Finset.mem_image, Finset.mem_filter,
    Finset.mem_inter, arithmeticProgression]
  constructor
  · rintro ⟨u, ⟨hu, huA⟩, rfl⟩
    exact ⟨huA, ⟨u, hu, rfl⟩⟩
  · rintro ⟨hxA, u, hu, hux⟩
    exact ⟨u, ⟨hu, hux ▸ hxA⟩, hux⟩

theorem card_affinePullback (A : Finset ℤ) (a : ℤ) (K L : ℕ) (hK : 0 < K) :
    (affinePullback A a K L).card = (A ∩ arithmeticProgression a K L).card := by
  rw [← affinePullback_image]
  symm
  apply Finset.card_image_of_injective
  intro u v huv
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hK) : (K : ℤ) ≠ 0)
    (add_left_cancel huv)

theorem density_affinePullback_ge (A : Finset ℤ) (a : ℤ) (K L : ℕ)
    (hK : 0 < K) (hL : 0 < L) (β δ : ℝ)
    (hgrowth : β * δ * (L : ℝ) ≤ ((A ∩ arithmeticProgression a K L).card : ℝ)) :
    β * δ ≤ setDensity L (affinePullback A a K L) := by
  unfold setDensity
  rw [card_affinePullback A a K L hK]
  exact (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr hgrowth

theorem pattern_affine_identity {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ∀ i, (P i).coeff 0 = 0) (q r x y : ℤ) (i : Fin (ℓ + 1)) :
    pattern P (r + q * x) (q * y) i =
      r + q * pattern (fun j => rescale (P j) q) x y i := by
  cases i using Fin.cases with
  | zero => simp [pattern]
  | succ i =>
    simp only [pattern, Fin.cons_succ]
    rw [← eval_rescale_mul (P i) q y (hP i)]
    ring

/-- An initial affine pullback inherits the exact forbidden configuration
condition, including distinctness and the actual unchanged PS prime. -/
theorem noRescaledConfiguration_of_no_original {ℓ : ℕ}
    (P : Fin ℓ → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (c : ℝ) (A B : Finset ℤ) (Q : ℕ) (hQ : 0 < Q) (r : ℤ)
    (himage : ∀ u ∈ B, r + (Q : ℤ) * u ∈ A)
    (hno : ¬ContainsConfiguration P c A) : NoRescaledConfiguration P Q c B := by
  rintro ⟨x, y, hy, hp, hmem, hdist⟩
  have hq : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hparam : ((Q * y + 1 : ℕ) : ℤ) - 1 = (Q : ℤ) * (y : ℤ) := by
    push_cast
    ring
  apply hno
  refine ⟨r + (Q : ℤ) * x, Q * y + 1, hp, ?_, ?_⟩
  · intro i
    rw [hparam, pattern_affine_identity P hP]
    exact himage _ (hmem i)
  · intro i j hij
    rw [hparam, pattern_affine_identity P hP, pattern_affine_identity P hP] at hij
    exact hdist (mul_left_cancel₀ hq (add_left_cancel hij))

theorem pattern_nested_affine_identity {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ∀ i, (P i).coeff 0 = 0) (q k a x y : ℤ) (hq : q ≠ 0)
    (i : Fin (ℓ + 1)) :
    pattern (fun j => rescale (P j) q) (a + k * x) (k * y) i =
      a + k * pattern (fun j => rescale (P j) (q * k)) x y i := by
  cases i using Fin.cases with
  | zero => simp [pattern]
  | succ i =>
    simp only [pattern, Fin.cons_succ]
    rw [← rescale_nested_eval (P i) q k y hq (hP i)]
    ring

/-- The invariant for the actual density-increment update. The parameter
prime `(Q*K)*y+1` is exactly `Q*(K*y)+1`, not an approximation. -/
theorem NoRescaledConfiguration.affine_pullback {ℓ : ℕ}
    (P : Fin ℓ → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (Q K : ℕ) (hQ : 0 < Q) (hK : 0 < K) (c : ℝ)
    (A B : Finset ℤ) (a : ℤ)
    (himage : ∀ u ∈ B, a + (K : ℤ) * u ∈ A)
    (hno : NoRescaledConfiguration P Q c A) :
    NoRescaledConfiguration P (Q * K) c B := by
  rintro ⟨x, y, hy, hp, hmem, hdist⟩
  have hq : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hk : (K : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  apply hno
  refine ⟨a + (K : ℤ) * x, K * y, by nlinarith, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_assoc] using hp
  · intro i
    rw [Nat.cast_mul, pattern_nested_affine_identity P hP _ _ _ _ _ hq]
    exact himage _ (by simpa only [Nat.cast_mul] using hmem i)
  · intro i j hij
    rw [Nat.cast_mul, pattern_nested_affine_identity P hP _ _ _ _ _ hq,
      pattern_nested_affine_identity P hP _ _ _ _ _ hq] at hij
    apply hdist
    simpa only [Nat.cast_mul] using mul_left_cancel₀ hk (add_left_cancel hij)

theorem NoRescaledConfiguration.progression_pullback {ℓ : ℕ}
    (P : Fin ℓ → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (Q : ℕ) (hQ : 0 < Q) (b L : ℕ) (c : ℝ) (A : Finset ℤ) (a : ℤ)
    (hno : NoRescaledConfiguration P Q c A) :
    NoRescaledConfiguration P (Q ^ (b + 1)) c (affinePullback A a (Q ^ b) L) := by
  have h := NoRescaledConfiguration.affine_pullback P hP Q (Q ^ b) hQ (pow_pos hQ b) c
    A (affinePullback A a (Q ^ b) L) a
    (fun u hu => (Finset.mem_filter.mp hu).2) hno
  simpa only [pow_succ'] using h

end PSPrimes
