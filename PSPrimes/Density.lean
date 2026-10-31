import Mathlib

/-!
# Finite density increment estimates

These lemmas implement the equal-mass estimate and the finite growth
contradiction used in Proposition 3.1 and the proof of Theorem 1.1.
They do not establish the external prime-to-integer comparison, the
arithmetic progression partitions, or the scale bounds needed to iterate.
-/

namespace PSPrimes

open scoped BigOperators

/-- The equal-mass estimate in the proof of Proposition 3.1.
The domain is the whole finite interval (or any finite set), so that the
reference function is the constant `δ` on this domain. -/
theorem sum_abs_sub_le_of_sum_eq {ι : Type*} (s : Finset ι)
    (F : ι → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hmass : ∑ x ∈ s, F x = (s.card : ℝ) * δ)
    (hupper : ∀ x ∈ s, F x ≤ (1 + ε) * δ) :
    ∑ x ∈ s, |F x - δ| ≤ 2 * ε * δ * (s.card : ℝ) := by
  have hεδ : 0 ≤ ε * δ := mul_nonneg hε hδ
  calc
    ∑ x ∈ s, |F x - δ| ≤ ∑ x ∈ s, (δ - F x + 2 * ε * δ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply abs_le.mpr
      constructor
      · nlinarith
      · have := hupper x hx
        nlinarith
    _ = 2 * ε * δ * (s.card : ℝ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      rw [hmass]
      ring

/-- A product of `R`-bounded complex numbers has norm at most `R^card`. -/
theorem norm_prod_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {R : ℝ} (hf : ∀ i ∈ s, ‖f i‖ ≤ R) :
    ‖∏ i ∈ s, f i‖ ≤ R ^ s.card := by
  calc
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i ∈ s, R := Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) hf
    _ = R ^ s.card := by simp

/-- Pointwise telescoping estimate for the difference of products.
The exponent is one less than the number of factors, as in the manuscript.
The empty product is allowed and both sides then vanish. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ i ∈ s, ‖f i‖ ≤ R)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ R) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤
      R ^ (s.card - 1) * ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ R := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ R := fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_not_mem ha,
      Finset.sum_insert ha, Nat.add_sub_cancel]
    by_cases hs : s = ∅
    · subst s
      simp
    · have hcard : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      have hpow : R * R ^ (s.card - 1) = R ^ s.card := by
        rw [← pow_succ']
        congr 1
        omega
      calc
        ‖f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i‖ =
            ‖(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by congr 1; ring
        _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ +
              ‖g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := norm_add_le _ _
        _ = ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
              ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖f a - g a‖ * R ^ s.card +
              R * (R ^ (s.card - 1) * ∑ i ∈ s, ‖f i - g i‖) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (norm_prod_le_pow s f hfs) (norm_nonneg _)
          · exact mul_le_mul hga (ih hfs hgs) (norm_nonneg _) hR
        _ = R ^ s.card * (‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖) := by
          rw [← mul_assoc R, hpow]
          ring

/-- Telescoping followed by the triangle inequality, with both sums finite.
This is the substantive estimate for the local-factor counting form before
using invariance of integer sums under translation. -/
theorem norm_sum_prod_sub_prod_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (F G : ι → κ → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hF : ∀ i ∈ s, ∀ x ∈ t, ‖F i x‖ ≤ R)
    (hG : ∀ i ∈ s, ∀ x ∈ t, ‖G i x‖ ≤ R) :
    ‖∑ x ∈ t, ((∏ i ∈ s, F i x) - ∏ i ∈ s, G i x)‖ ≤
      R ^ (s.card - 1) * ∑ i ∈ s, ∑ x ∈ t, ‖F i x - G i x‖ := by
  calc
    ‖∑ x ∈ t, ((∏ i ∈ s, F i x) - ∏ i ∈ s, G i x)‖ ≤
        ∑ x ∈ t, ‖(∏ i ∈ s, F i x) - ∏ i ∈ s, G i x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ t, R ^ (s.card - 1) * ∑ i ∈ s, ‖F i x - G i x‖ := by
      apply Finset.sum_le_sum
      intro x hx
      exact norm_prod_sub_prod_le s (fun i ↦ F i x) (fun i ↦ G i x) hR
        (fun i hi ↦ hF i hi x hx) (fun i hi ↦ hG i hi x hx)
    _ = R ^ (s.card - 1) * ∑ i ∈ s, ∑ x ∈ t, ‖F i x - G i x‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]

/-- Restricting a translate of an absolutely summable, finitely supported
quantity can only reduce its finite `ℓ¹` mass. No periodic or cyclic model
is used: both the support and the translation lie in the integers. -/
theorem sum_translated_abs_sub_le (U V : Finset ℤ) (F : ℤ → ℝ)
    (δ : ℝ) (a : ℤ) (hsupport : ∀ x ∉ U, F x = 0) :
    ∑ x ∈ V, |F (x + a) - (if x + a ∈ U then δ else 0)| ≤
      ∑ x ∈ U, |F x - δ| := by
  classical
  let H : ℤ → ℝ := fun x ↦ |F x - (if x ∈ U then δ else 0)|
  have hH : ∀ x ∉ U, H x = 0 := by
    intro x hx
    simp [H, hx, hsupport x hx]
  calc
    ∑ x ∈ V, |F (x + a) - (if x + a ∈ U then δ else 0)| =
        ∑ x ∈ V.image (fun x ↦ x + a), H x := by
      symm
      apply Finset.sum_image
      intro x hx y hy hxy
      exact add_right_cancel hxy
    _ ≤ ∑ x ∈ V.image (fun x ↦ x + a) ∪ U, H x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro x hx _
      exact abs_nonneg _
    _ = ∑ x ∈ U, H x := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x hx hxU
      exact hH x hxU
    _ = ∑ x ∈ U, |F x - δ| := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [H, hx]

/-- The unnormalized difference of the two local-factor counting forms.
The factors include the zeroth factor. `V` is an arbitrary finite part of
`ℤ`, and the integer shifts are arbitrary, so the estimate applies to the
polynomials in the manuscript without a cyclic model or boundary convention. -/
noncomputable def localFactorDifference {ι κ : Type*} (I : Finset ι)
    (U V : Finset ℤ) (J : Finset κ) (R : ι → κ → ℤ)
    (F : ι → ℤ → ℝ) (δ : ℝ) : ℂ :=
  ∑ y ∈ J, ∑ x ∈ V,
    ((∏ i ∈ I, (F i (x + R i y) : ℂ)) -
      ∏ i ∈ I, (if x + R i y ∈ U then (δ : ℂ) else 0))

/-- The complete local-factor counting estimate in the proof of
Proposition 3.1, before dividing by the number of `x` and `y` values.
The exponent is the number of factors minus one. -/
theorem localFactorDifference_bound {ι κ : Type*} (I : Finset ι)
    (U V : Finset ℤ) (J : Finset κ) (R : ι → κ → ℤ)
    (F : ι → ℤ → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hpos : ∀ i ∈ I, ∀ x, 0 ≤ F i x)
    (hsupport : ∀ i ∈ I, ∀ x ∉ U, F i x = 0)
    (hmass : ∀ i ∈ I, ∑ x ∈ U, F i x = (U.card : ℝ) * δ)
    (hupper : ∀ i ∈ I, ∀ x ∈ U, F i x ≤ (1 + ε) * δ) :
    ‖localFactorDifference I U V J R F δ‖ ≤
      (J.card : ℝ) * ((1 + ε) * δ) ^ (I.card - 1) * (I.card : ℝ) *
        (2 * ε * δ * (U.card : ℝ)) := by
  classical
  let Rb : ℝ := (1 + ε) * δ
  have hRb : 0 ≤ Rb := mul_nonneg (by linarith) hδ
  have hδRb : δ ≤ Rb := by dsimp [Rb]; nlinarith [mul_nonneg hε hδ]
  have hF : ∀ i ∈ I, ∀ x, ‖(F i x : ℂ)‖ ≤ Rb := by
    intro i hi x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos i hi x)]
    by_cases hx : x ∈ U
    · exact hupper i hi x hx
    · rw [hsupport i hi x hx]
      exact hRb
  have hG : ∀ x : ℤ, ‖(if x ∈ U then (δ : ℂ) else 0)‖ ≤ Rb := by
    intro x
    split_ifs
    · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ] using hδRb
    · simpa using hRb
  have hsingle : ∀ y : κ,
      ‖∑ x ∈ V, ((∏ i ∈ I, (F i (x + R i y) : ℂ)) -
        ∏ i ∈ I, (if x + R i y ∈ U then (δ : ℂ) else 0))‖ ≤
        Rb ^ (I.card - 1) * (I.card : ℝ) * (2 * ε * δ * (U.card : ℝ)) := by
    intro y
    calc
      ‖∑ x ∈ V, ((∏ i ∈ I, (F i (x + R i y) : ℂ)) -
          ∏ i ∈ I, (if x + R i y ∈ U then (δ : ℂ) else 0))‖ ≤
          Rb ^ (I.card - 1) * ∑ i ∈ I, ∑ x ∈ V,
            ‖(F i (x + R i y) : ℂ) -
              (if x + R i y ∈ U then (δ : ℂ) else 0)‖ :=
        norm_sum_prod_sub_prod_le I V _ _ hRb
          (fun i hi x _ ↦ hF i hi _) (fun i _ x _ ↦ hG _)
      _ ≤ Rb ^ (I.card - 1) * ∑ _i ∈ I, (2 * ε * δ * (U.card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hRb _)
        apply Finset.sum_le_sum
        intro i hi
        have hnorm : ∀ x : ℤ,
            ‖(F i (x + R i y) : ℂ) -
              (if x + R i y ∈ U then (δ : ℂ) else 0)‖ =
              |F i (x + R i y) - (if x + R i y ∈ U then δ else 0)| := by
          intro x
          split_ifs <;> simp [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simp_rw [hnorm]
        exact (sum_translated_abs_sub_le U V (F i) δ (R i y) (hsupport i hi)).trans
          (sum_abs_sub_le_of_sum_eq U (F i) hδ hε (hmass i hi) (hupper i hi))
      _ = Rb ^ (I.card - 1) * (I.card : ℝ) * (2 * ε * δ * (U.card : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  calc
    ‖localFactorDifference I U V J R F δ‖ ≤
        ∑ y ∈ J, ‖∑ x ∈ V, ((∏ i ∈ I, (F i (x + R i y) : ℂ)) -
          ∏ i ∈ I, (if x + R i y ∈ U then (δ : ℂ) else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ _y ∈ J, Rb ^ (I.card - 1) * (I.card : ℝ) *
        (2 * ε * δ * (U.card : ℝ)) := Finset.sum_le_sum (fun y _ ↦ hsingle y)
    _ = (J.card : ℝ) * ((1 + ε) * δ) ^ (I.card - 1) * (I.card : ℝ) *
        (2 * ε * δ * (U.card : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Rb]
      ring

/-- After the exact normalization by `|U| |J|`, the bound has the form
`2 k ε (1+ε)^(k-1) δ^k`, with `k` factors including the zeroth one. -/
theorem normalized_localFactorDifference_bound {ι κ : Type*} (I : Finset ι)
    (U V : Finset ℤ) (J : Finset κ) (R : ι → κ → ℤ)
    (F : ι → ℤ → ℝ) {δ ε : ℝ} (hI : I.Nonempty) (hU : U.Nonempty)
    (hJ : J.Nonempty) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hpos : ∀ i ∈ I, ∀ x, 0 ≤ F i x)
    (hsupport : ∀ i ∈ I, ∀ x ∉ U, F i x = 0)
    (hmass : ∀ i ∈ I, ∑ x ∈ U, F i x = (U.card : ℝ) * δ)
    (hupper : ∀ i ∈ I, ∀ x ∈ U, F i x ≤ (1 + ε) * δ) :
    ‖(((U.card : ℂ) * (J.card : ℂ))⁻¹) * localFactorDifference I U V J R F δ‖ ≤
      2 * (I.card : ℝ) * ε * (1 + ε) ^ (I.card - 1) * δ ^ I.card := by
  have hUc : 0 < (U.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hU)
  have hJc : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
  have hden : 0 < (U.card : ℝ) * (J.card : ℝ) := mul_pos hUc hJc
  have hpow : δ ^ (I.card - 1) * δ = δ ^ I.card := by
    rw [← pow_succ]
    congr 1
    have := Finset.card_pos.mpr hI
    omega
  calc
    ‖(((U.card : ℂ) * (J.card : ℂ))⁻¹) * localFactorDifference I U V J R F δ‖ =
        ((U.card : ℝ) * (J.card : ℝ))⁻¹ * ‖localFactorDifference I U V J R F δ‖ := by
      simp only [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((U.card : ℝ) * (J.card : ℝ))⁻¹ *
        ((J.card : ℝ) * ((1 + ε) * δ) ^ (I.card - 1) * (I.card : ℝ) *
          (2 * ε * δ * (U.card : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (localFactorDifference_bound I U V J R F hδ hε hpos hsupport hmass hupper)
        (inv_nonneg.mpr hden.le)
    _ = ((1 + ε) * δ) ^ (I.card - 1) * (I.card : ℝ) * (2 * ε * δ) := by
      field_simp
      ring
    _ = 2 * (I.card : ℝ) * ε * (1 + ε) ^ (I.card - 1) * δ ^ I.card := by
      rw [mul_pow]
      calc
        (1 + ε) ^ (I.card - 1) * δ ^ (I.card - 1) * (I.card : ℝ) * (2 * ε * δ) =
            2 * (I.card : ℝ) * ε * (1 + ε) ^ (I.card - 1) * (δ ^ (I.card - 1) * δ) := by ring
        _ = _ := by rw [hpow]

/-- A discrepancy larger than the telescoping bound forces a local density
above `(1+ε)δ`. This is the contradiction argument in Proposition 3.1;
construction and arithmetic-progression structure of the partitions are
separate obligations. -/
theorem exists_large_local_factor {ι κ : Type*} (I : Finset ι)
    (U V : Finset ℤ) (J : Finset κ) (R : ι → κ → ℤ)
    (F : ι → ℤ → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hpos : ∀ i ∈ I, ∀ x, 0 ≤ F i x)
    (hsupport : ∀ i ∈ I, ∀ x ∉ U, F i x = 0)
    (hmass : ∀ i ∈ I, ∑ x ∈ U, F i x = (U.card : ℝ) * δ)
    (hdiscrepancy : (J.card : ℝ) * ((1 + ε) * δ) ^ (I.card - 1) *
      (I.card : ℝ) * (2 * ε * δ * (U.card : ℝ)) <
        ‖localFactorDifference I U V J R F δ‖) :
    ∃ i ∈ I, ∃ x ∈ U, (1 + ε) * δ < F i x := by
  by_contra h
  push_neg at h
  exact (not_lt_of_ge (localFactorDifference_bound I U V J R F hδ hε hpos
    hsupport hmass h)) hdiscrepancy

/-- Relative density on a finite atom, with the usual totalized division
convention at an empty atom. The partition lemmas use nonempty atoms. -/
noncomputable def atomDensity (A B : Finset ℤ) : ℝ := (A ∩ B).card / (B.card : ℝ)

/-- The local-factor function of a finite partition has exactly the same
mass as the original set. This proves the equal-mass input used above;
it is not an assumption about conditional expectations. -/
theorem sum_partition_density (A U : Finset ℤ) (cells : Finset (Finset ℤ))
    (F : ℤ → ℝ) (hA : A ⊆ U) (hcover : cells.biUnion id = U)
    (hdisj : (cells : Set (Finset ℤ)).PairwiseDisjoint id)
    (hnonempty : ∀ B ∈ cells, B.Nonempty)
    (hF : ∀ B ∈ cells, ∀ x ∈ B, F x = atomDensity A B) :
    ∑ x ∈ U, F x = (A.card : ℝ) := by
  classical
  have hdisj' : (cells : Set (Finset ℤ)).PairwiseDisjoint (fun B ↦ A ∩ B) :=
    hdisj.mono (fun _ ↦ Finset.inter_subset_right)
  have hcover' : cells.biUnion (fun B ↦ B) = U := hcover
  have hsumcard : (∑ B ∈ cells, (A ∩ B).card) = A.card := by
    have h := Finset.card_biUnion hdisj'
    rw [← Finset.inter_biUnion, hcover', Finset.inter_eq_left.mpr hA] at h
    exact h.symm
  have hsumcardR : (∑ B ∈ cells, ((A ∩ B).card : ℝ)) = (A.card : ℝ) := by
    exact_mod_cast hsumcard
  calc
    ∑ x ∈ U, F x = ∑ B ∈ cells, ∑ x ∈ B, F x := by
      rw [← hcover, Finset.sum_biUnion hdisj]
      rfl
    _ = ∑ B ∈ cells, ((A ∩ B).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro B hB
      calc
        ∑ x ∈ B, F x = ∑ _x ∈ B, atomDensity A B :=
          Finset.sum_congr rfl (fun x hx ↦ hF B hB x hx)
        _ = ((A ∩ B).card : ℝ) := by
          have hBc : (B.card : ℝ) ≠ 0 :=
            ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (hnonempty B hB)))
          simp only [Finset.sum_const, nsmul_eq_mul, atomDensity]
          field_simp
    _ = (A.card : ℝ) := hsumcardR

/-- A large local factor gives an actual atom whose set density is larger
than the specified threshold. The membership witness ensures the atom
is nonempty and hence justifies clearing its density denominator. -/
theorem exists_dense_atom_of_large_factor (A U : Finset ℤ)
    (cells : Finset (Finset ℤ)) (F : ℤ → ℝ) (threshold : ℝ)
    (hcover : ∀ x ∈ U, ∃ B ∈ cells, x ∈ B)
    (hF : ∀ B ∈ cells, ∀ x ∈ B, F x = atomDensity A B)
    (hlarge : ∃ x ∈ U, threshold < F x) :
    ∃ B ∈ cells, threshold * (B.card : ℝ) < ((A ∩ B).card : ℝ) := by
  obtain ⟨x, hxU, hx⟩ := hlarge
  obtain ⟨B, hB, hxB⟩ := hcover x hxU
  refine ⟨B, hB, ?_⟩
  have hBc : 0 < (B.card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x, hxB⟩)
  rw [hF B hB x hxB] at hx
  exact (lt_div_iff₀ hBc).mp hx

/-- The local part of Proposition 3.1 in full: genuine partition averages,
equal mass proved from the partitions, the exact normalized discrepancy,
and extraction of an atom with increased density. The construction of the
partitions, their progression structure and their resolution lower bound
remain the separate external/local-factor approximation steps. -/
theorem density_increment_from_local_discrepancy {ι κ : Type*} (I : Finset ι)
    (A U V : Finset ℤ) (J : Finset κ) (R : ι → κ → ℤ)
    (cells : ι → Finset (Finset ℤ)) (F : ι → ℤ → ℝ) {δ ε : ℝ}
    (hI : I.Nonempty) (hU : U.Nonempty) (hJ : J.Nonempty)
    (hA : A ⊆ U) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdensity : (A.card : ℝ) = (U.card : ℝ) * δ)
    (hcover : ∀ i ∈ I, (cells i).biUnion id = U)
    (hdisj : ∀ i ∈ I, (cells i : Set (Finset ℤ)).PairwiseDisjoint id)
    (hnonempty : ∀ i ∈ I, ∀ B ∈ cells i, B.Nonempty)
    (hF : ∀ i ∈ I, ∀ B ∈ cells i, ∀ x ∈ B, F i x = atomDensity A B)
    (hsupport : ∀ i ∈ I, ∀ x ∉ U, F i x = 0)
    (hdiscrepancy : 2 * (I.card : ℝ) * ε * (1 + ε) ^ (I.card - 1) * δ ^ I.card <
      ‖(((U.card : ℂ) * (J.card : ℂ))⁻¹) * localFactorDifference I U V J R F δ‖) :
    ∃ i ∈ I, ∃ B ∈ cells i,
      ((1 + ε) * δ) * (B.card : ℝ) < ((A ∩ B).card : ℝ) := by
  classical
  have hpos : ∀ i ∈ I, ∀ x, 0 ≤ F i x := by
    intro i hi x
    by_cases hx : x ∈ U
    · rw [← hcover i hi] at hx
      obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hx
      rw [hF i hi B hB x hxB]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [hsupport i hi x hx]
  have hmass : ∀ i ∈ I, ∑ x ∈ U, F i x = (U.card : ℝ) * δ := by
    intro i hi
    rw [sum_partition_density A U (cells i) (F i) hA (hcover i hi)
      (hdisj i hi) (hnonempty i hi) (hF i hi), hdensity]
  by_contra h
  push_neg at h
  have hupper : ∀ i ∈ I, ∀ x ∈ U, F i x ≤ (1 + ε) * δ := by
    intro i hi x hx
    rw [← hcover i hi] at hx
    obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hx
    rw [hF i hi B hB x hxB]
    have hBc : 0 < (B.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x, hxB⟩)
    exact (div_le_iff₀ hBc).mpr (h i hi B hB)
  exact (not_lt_of_ge (normalized_localFactorDifference_bound I U V J R F
    hI hU hJ hδ hε hpos hsupport hmass hupper)) hdiscrepancy

/-- Iterating multiplicative density growth over a finite number of steps. -/
theorem density_growth_lower_bound (δ : ℕ → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (T : ℕ) (hstep : ∀ n < T, β * δ n ≤ δ (n + 1)) :
    β ^ T * δ 0 ≤ δ T := by
  induction T with
  | zero => simp
  | succ T ih =>
    have ih' := ih (fun n hn ↦ hstep n (Nat.lt_trans hn (Nat.lt_succ_self T)))
    calc
      β ^ (T + 1) * δ 0 = β * (β ^ T * δ 0) := by ring
      _ ≤ β * δ T := mul_le_mul_of_nonneg_left ih' hβ
      _ ≤ δ (T + 1) := hstep T (Nat.lt_succ_self T)

/-- The final contradiction once the scale analysis permits enough increments. -/
theorem density_growth_contradiction (δ : ℕ → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (T : ℕ) (hstep : ∀ n < T, β * δ n ≤ δ (n + 1))
    (hbound : δ T ≤ 1) (hlarge : 1 < β ^ T * δ 0) : False := by
  have := density_growth_lower_bound δ hβ T hstep
  linarith

/-- A positive initial density and a fixed growth factor greater than one
specify a finite horizon after which no density-bounded chain can exist. -/
theorem exists_density_growth_horizon {α β : ℝ} (hα : 0 < α) (hβ : 1 < β) :
    ∃ T : ℕ, ∀ δ : ℕ → ℝ, α ≤ δ 0 →
      (∀ n < T, β * δ n ≤ δ (n + 1)) → δ T ≤ 1 → False := by
  obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt (1 / α) hβ
  refine ⟨T, fun δ hδ hstep hbound ↦ ?_⟩
  apply density_growth_contradiction δ (le_trans (by norm_num) (le_of_lt hβ)) T hstep hbound
  have hT' : 1 < β ^ T * α := (div_lt_iff₀ hα).mp hT
  exact lt_of_lt_of_le hT' (mul_le_mul_of_nonneg_left hδ (pow_nonneg (by linarith) _))

end PSPrimes
