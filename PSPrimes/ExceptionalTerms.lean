import PSPrimes.Definitions
import PSPrimes.Rescaling

/-!
# Elementary bounds for weights and collision parameters

These are exact finite supporting estimates for Lemma 3.2 and Proposition 2.3.
Higher prime powers and the asymptotic comparison are separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

theorem sparseMangoldt_le_envelope {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    {n L : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L) :
    sparseMangoldt γ n ≤ γ⁻¹ * (L : ℝ) ^ (1 - γ) * Real.log L := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hL₀ : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hlog : ArithmeticFunction.vonMangoldt n ≤ Real.log L :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hn₀ (by exact_mod_cast hnL))
  have hpow : (n : ℝ) ^ (1 - γ) ≤ (L : ℝ) ^ (1 - γ) :=
    Real.rpow_le_rpow hn₀.le (by exact_mod_cast hnL) (by linarith)
  unfold sparseMangoldt
  split_ifs
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hγ₀.le)
    · exact hlog
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact mul_nonneg (inv_nonneg.mpr hγ₀.le) (Real.rpow_nonneg hL₀ _)
  · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ₀.le)
      (Real.rpow_nonneg hL₀ _)) (Real.log_natCast_nonneg L)

theorem discrepancyWeight_le_envelope {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    {n L : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L) :
    |discrepancyWeight γ n| ≤ (γ⁻¹ + 1) * (L : ℝ) ^ (1 - γ) * Real.log L := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast hn.trans hnL
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : ArithmeticFunction.vonMangoldt n ≤ Real.log L :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hn₀ (by exact_mod_cast hnL))
  have hpow : (1 : ℝ) ≤ (L : ℝ) ^ (1 - γ) :=
    Real.one_le_rpow hL (by linarith)
  calc
    |discrepancyWeight γ n| ≤ |sparseMangoldt γ n| +
        |ArithmeticFunction.vonMangoldt n| := abs_sub _ _
    _ = sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n := by
      rw [abs_of_nonneg (sparseMangoldt_nonneg hγ₀ n),
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ γ⁻¹ * (L : ℝ) ^ (1 - γ) * Real.log L +
        (L : ℝ) ^ (1 - γ) * Real.log L := by
      apply add_le_add (sparseMangoldt_le_envelope hγ₀ hγ₁ hn hnL)
      exact hlog.trans (by nlinarith [Real.log_natCast_nonneg L])
    _ = (γ⁻¹ + 1) * (L : ℝ) ^ (1 - γ) * Real.log L := by ring

/-- A nonzero integer polynomial has at most its degree many roots in any finite set. -/
theorem card_zeroParameters_le (p : Polynomial ℤ) (hp : p ≠ 0) (s : Finset ℤ) :
    (s.filter (fun y => p.eval y = 0)).card ≤ p.natDegree := by
  classical
  by_contra h
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p
      (s.filter (fun y => p.eval y = 0))
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · omega

/-- All unordered index pairs are represented exactly once by i<j. -/
def indexPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

/-- The actual integer parameters where two polynomial offsets coincide. -/
def collisionParameters {k : ℕ} (R : Fin k → Polynomial ℤ) (s : Finset ℤ) : Finset ℤ :=
  s.filter (fun y => ∃ i j, i < j ∧ (R i).eval y = (R j).eval y)

/-- Finite union of root sets gives the precise sum-of-degrees collision bound. -/
theorem card_collisionParameters_le {k : ℕ} (R : Fin k → Polynomial ℤ)
    (hR : Function.Injective R) (s : Finset ℤ) :
    (collisionParameters R s).card ≤
      ∑ ij ∈ indexPairs k, (R ij.1 - R ij.2).natDegree := by
  classical
  let zeros : Fin k × Fin k → Finset ℤ :=
    fun ij => s.filter (fun y => (R ij.1 - R ij.2).eval y = 0)
  have hsub : collisionParameters R s ⊆ (indexPairs k).biUnion zeros := by
    intro y hy
    obtain ⟨hy, i, j, hij, heq⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_biUnion.mpr
    refine ⟨(i, j), ?_, ?_⟩
    · simp [indexPairs, hij]
    · simp [zeros, hy, heq]
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro ij hij
  apply card_zeroParameters_le
  apply sub_ne_zero.mpr
  exact fun heq => (ne_of_lt (Finset.mem_filter.mp hij).2) (hR heq)

/-- A common maximum degree makes the number of exceptional parameters uniform. -/
theorem card_collisionParameters_le_degree_mul_pairs {k d : ℕ}
    (R : Fin k → Polynomial ℤ) (hR : Function.Injective R)
    (hdeg : ∀ i, (R i).natDegree ≤ d) (s : Finset ℤ) :
    (collisionParameters R s).card ≤ (indexPairs k).card * d := by
  apply (card_collisionParameters_le R hR s).trans
  calc
    (∑ ij ∈ indexPairs k, (R ij.1 - R ij.2).natDegree) ≤
        ∑ _ij ∈ indexPairs k, d := by
      apply Finset.sum_le_sum
      intro ij hij
      exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hdeg _) (hdeg _))
    _ = (indexPairs k).card * d := by simp

@[simp] theorem card_indexPairs (k : ℕ) : (indexPairs k).card = k.choose 2 := by
  classical
  calc
    (indexPairs k).card = ((Finset.univ : Finset (Fin k)).powersetCard 2).card := by
      apply Finset.card_bij (fun ij _ => ({ij.1, ij.2} : Finset (Fin k)))
      · intro ij hij
        apply Finset.mem_powersetCard.mpr
        exact ⟨Finset.subset_univ _, Finset.card_pair (ne_of_lt (Finset.mem_filter.mp hij).2)⟩
      · intro ij hij kl hkl heq
        have h1 : ij.1 = kl.1 ∨ ij.1 = kl.2 := by
          have hm : ij.1 ∈ ({ij.1, ij.2} : Finset (Fin k)) := by simp
          rw [heq] at hm
          simpa using hm
        have h2 : ij.2 = kl.1 ∨ ij.2 = kl.2 := by
          have hm : ij.2 ∈ ({ij.1, ij.2} : Finset (Fin k)) := by simp
          rw [heq] at hm
          simpa using hm
        have hi := (Finset.mem_filter.mp hij).2
        have hk := (Finset.mem_filter.mp hkl).2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · omega
        · exact Prod.ext h1 h2
        · omega
        · omega
      · intro t ht
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp ht).2
        rcases lt_or_gt_of_ne hxy with hlt | hlt
        · refine ⟨(x, y), ?_, rfl⟩
          simp [indexPairs, hlt]
        · refine ⟨(y, x), ?_, ?_⟩
          · simp [indexPairs, hlt]
          · exact Finset.pair_comm _ _
    _ = k.choose 2 := by simp [Finset.card_powersetCard]

/-- At most d times binomial(k,2) parameters can cause an offset collision. -/
theorem card_collisionParameters_le_choose {k d : ℕ} (R : Fin k → Polynomial ℤ)
    (hR : Function.Injective R) (hdeg : ∀ i, (R i).natDegree ≤ d) (s : Finset ℤ) :
    (collisionParameters R s).card ≤ d * k.choose 2 := by
  simpa [Nat.mul_comm] using card_collisionParameters_le_degree_mul_pairs R hR hdeg s

/-- The root-set definition is exactly failure of distinctness of the polynomial offsets. -/
theorem mem_collisionParameters_iff {k : ℕ} (R : Fin k → Polynomial ℤ)
    (s : Finset ℤ) (y : ℤ) :
    y ∈ collisionParameters R s ↔ y ∈ s ∧
      ¬Function.Injective (fun i => (R i).eval y) := by
  classical
  simp only [collisionParameters, Finset.mem_filter]
  constructor
  · rintro ⟨hy, i, j, hij, heq⟩
    exact ⟨hy, fun hinj => (ne_of_lt hij) (hinj heq)⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    by_contra hno
    apply h
    intro i j heq
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hno ⟨i, j, hlt, heq⟩
    · exact hno ⟨j, i, hlt, heq.symm⟩

/-- A zero offset adjoined to positive-degree, distinct integer polynomials remains distinct. -/
theorem zeroExtended_injective {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : Function.Injective P) (hpos : ∀ i, 0 < (P i).natDegree) :
    Function.Injective (Fin.cons (0 : Polynomial ℤ) P) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      have hp : P j = 0 := by simpa using hij.symm
      have := hpos j
      rw [hp, Polynomial.natDegree_zero] at this
      omega
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have hp : P i = 0 := by simpa using hij
      have := hpos i
      rw [hp, Polynomial.natDegree_zero] at this
      omega
    | succ j =>
      apply congrArg Fin.succ
      apply hP
      simpa using hij

/-- Uniform collision count for the actual rescaled families, including P₀=0. -/
theorem card_rescaled_collisions_le {ℓ d : ℕ} (P : PolynomialFamily ℓ)
    (q : ℤ) (hq : q ≠ 0) (hdeg : ∀ i, (P.polynomials i).natDegree ≤ d)
    (s : Finset ℤ) :
    (collisionParameters (Fin.cons (0 : Polynomial ℤ)
      (fun i => rescale (P.polynomials i) q)) s).card ≤ d * (ℓ + 1).choose 2 := by
  have hdegrees (i : Fin ℓ) : (rescale (P.polynomials i) q).natDegree =
      (P.polynomials i).natDegree :=
    natDegree_rescale _ _ hq (lt_of_lt_of_le Nat.zero_lt_one (P.positive_degree i))
  apply card_collisionParameters_le_choose
  · apply zeroExtended_injective
    · intro i j hij
      apply P.increasing_degrees.injective
      have h := congrArg Polynomial.natDegree hij
      simpa only [hdegrees] using h
    · intro i
      rw [hdegrees]
      exact lt_of_lt_of_le Nat.zero_lt_one (P.positive_degree i)
  · intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa only [Fin.cons_succ, hdegrees] using hdeg i

/-- A bounded weighted sum over the actual collision set has a degree-only bound. -/
theorem norm_collisionSum_le {k d : ℕ} (R : Fin k → Polynomial ℤ)
    (hR : Function.Injective R) (hdeg : ∀ i, (R i).natDegree ≤ d)
    (s : Finset ℤ) (f : ℤ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ y ∈ collisionParameters R s, ‖f y‖ ≤ B) :
    ‖∑ y ∈ collisionParameters R s, f y‖ ≤ (d * k.choose 2 : ℕ) * B := by
  calc
    ‖∑ y ∈ collisionParameters R s, f y‖ ≤
        ∑ y ∈ collisionParameters R s, ‖f y‖ := norm_sum_le _ _
    _ ≤ ∑ _y ∈ collisionParameters R s, B := Finset.sum_le_sum hf
    _ = ((collisionParameters R s).card : ℝ) * B := by simp
    _ ≤ (d * k.choose 2 : ℕ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_collisionParameters_le_choose R hR hdeg s) hB

/-- Normalize the actual double sum over collision parameters.
The spatial support has at most N points; every summand has norm at most B.
This gives the manuscript's degree-dependent collision cost O(B/M). -/
theorem norm_collisionDoubleSum_normalized_le {k d N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (R : Fin k → Polynomial ℤ)
    (hR : Function.Injective R) (hdeg : ∀ i, (R i).natDegree ≤ d)
    (spatial parameters : Finset ℤ) (hspatial : spatial.card ≤ N)
    (term : ℤ → ℤ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hterm : ∀ x ∈ spatial, ∀ y ∈ collisionParameters R parameters, ‖term x y‖ ≤ B) :
    ‖((N : ℂ) * (M : ℂ))⁻¹ *
      ∑ x ∈ spatial, ∑ y ∈ collisionParameters R parameters, term x y‖ ≤
        (d * k.choose 2 : ℕ) * B / (M : ℝ) := by
  have hinner (x : ℤ) (hx : x ∈ spatial) :
      ‖∑ y ∈ collisionParameters R parameters, term x y‖ ≤
        (d * k.choose 2 : ℕ) * B :=
    norm_collisionSum_le R hR hdeg parameters (term x) hB (hterm x hx)
  have hsum : ‖∑ x ∈ spatial, ∑ y ∈ collisionParameters R parameters, term x y‖ ≤
      (N : ℝ) * ((d * k.choose 2 : ℕ) * B) := by
    calc
      ‖∑ x ∈ spatial, ∑ y ∈ collisionParameters R parameters, term x y‖ ≤
          ∑ x ∈ spatial, ‖∑ y ∈ collisionParameters R parameters, term x y‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ spatial, (d * k.choose 2 : ℕ) * B := Finset.sum_le_sum hinner
      _ = (spatial.card : ℝ) * ((d * k.choose 2 : ℕ) * B) := by simp
      _ ≤ (N : ℝ) * ((d * k.choose 2 : ℕ) * B) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hspatial) (mul_nonneg (Nat.cast_nonneg _) hB)
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  calc
    ((N : ℝ) * (M : ℝ))⁻¹ *
        ‖∑ x ∈ spatial, ∑ y ∈ collisionParameters R parameters, term x y‖ ≤
        ((N : ℝ) * (M : ℝ))⁻¹ * ((N : ℝ) * ((d * k.choose 2 : ℕ) * B)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    _ = (d * k.choose 2 : ℕ) * B / (M : ℝ) := by
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      field_simp
      ring

end PSPrimes
