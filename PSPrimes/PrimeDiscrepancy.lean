import PSPrimes.Counting
import PSPrimes.ExceptionalTerms
import PSPrimes.PrimePowers
import PSPrimes.Scales
import PSPrimes.RecurrenceDefinitions
import PSPrimes.ModelOverlap
import PSPrimes.PolynomialBounds
import PSPrimes.PrimeMassInputs

/-!
# Finite discrepancy arguments for actual sets

This module connects absence of a configuration to actual finite counting
forms. The arithmetic prime-progression mass inputs are kept separately.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

attribute [local instance] Classical.propDecidable

def setDensity (N : ℕ) (A : Finset ℤ) : ℝ := (A.card : ℝ) / N

def setIndicator (A : Finset ℤ) (x : ℤ) : ℝ := if x ∈ A then 1 else 0

def indicatorFinsupp (A : Finset ℤ) : ℤ →₀ ℂ :=
  Finsupp.onFinset A (fun x => (setIndicator A x : ℂ)) (by
    intro x hx
    by_contra h
    simp [setIndicator, h] at hx)

@[simp] theorem indicatorFinsupp_apply (A : Finset ℤ) (x : ℤ) :
    indicatorFinsupp A x = (setIndicator A x : ℂ) := rfl

@[simp] theorem indicatorFinsupp_support (A : Finset ℤ) :
    (indicatorFinsupp A).support = A := by
  ext x
  simp [Finsupp.mem_support_iff, setIndicator]

@[simp] theorem setIndicator_of_mem {A : Finset ℤ} {x : ℤ} (hx : x ∈ A) :
    setIndicator A x = 1 := if_pos hx

@[simp] theorem setIndicator_of_not_mem {A : Finset ℤ} {x : ℤ} (hx : x ∉ A) :
    setIndicator A x = 0 := if_neg hx

theorem setIndicator_nonneg (A : Finset ℤ) (x : ℤ) : 0 ≤ setIndicator A x := by
  unfold setIndicator
  split_ifs <;> norm_num

theorem setIndicator_le_one (A : Finset ℤ) (x : ℤ) : setIndicator A x ≤ 1 := by
  unfold setIndicator
  split_ifs <;> norm_num

def patternIndicator {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (A : Finset ℤ) (x y : ℤ) : ℝ :=
  ∏ i, setIndicator A (x + (P i).eval y)

theorem patternIndicator_nonneg {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (A : Finset ℤ) (x y : ℤ) : 0 ≤ patternIndicator P A x y :=
  Finset.prod_nonneg (fun _ _ => setIndicator_nonneg A _)

theorem patternIndicator_le_one {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (A : Finset ℤ) (x y : ℤ) : patternIndicator P A x y ≤ 1 :=
  Finset.prod_le_one (fun _ _ => setIndicator_nonneg A _) (fun _ _ => setIndicator_le_one A _)

theorem patternIndicator_eq_one {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (A : Finset ℤ) (x y : ℤ) (h : ∀ i, x + (P i).eval y ∈ A) :
    patternIndicator P A x y = 1 := by
  simp [patternIndicator, h]

theorem patternIndicator_ne_zero_iff {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (A : Finset ℤ) (x y : ℤ) :
    patternIndicator P A x y ≠ 0 ↔ ∀ i, x + (P i).eval y ∈ A := by
  simp [patternIndicator, Finset.prod_ne_zero_iff, setIndicator]

def setCountingForm {ℓ : ℕ} (N M Q : ℕ) (P : Fin ℓ → Polynomial ℤ)
    (w : ℕ → ℝ) (A : Finset ℤ) : ℝ :=
  ((N : ℝ) * (M : ℝ))⁻¹ * ∑ x ∈ A, ∑ y ∈ initialInterval M,
    w (Q * y + 1) * patternIndicator P A x (y : ℤ)

/-- The real set count is exactly the manuscript's complex counting form
with all indicator inputs; no new counting model is introduced. -/
theorem setCountingForm_eq_countingForm {ℓ : ℕ} (N M Q : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (w : ℕ → ℝ) (A : Finset ℤ) :
    (setCountingForm N M Q P w A : ℂ) =
      countingForm N M Q P (fun n => (w n : ℂ)) (indicatorFinsupp A)
        (fun _ x => (setIndicator A x : ℂ)) := by
  simp only [setCountingForm, countingForm, indicatorFinsupp_support,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum, Complex.ofReal_natCast,
    indicatorFinsupp_apply, patternIndicator, Complex.ofReal_prod]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp [setIndicator_of_mem hx]

/-- The exact rescaled forbidden-configuration hypothesis in Lemma 3.2. -/
def NoRescaledConfiguration {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (Q : ℕ) (c : ℝ) (A : Finset ℤ) : Prop :=
  ¬∃ (x : ℤ) (y : ℕ), 1 ≤ y ∧ IsPSPrime c (Q * y + 1) ∧
    (∀ i, pattern (fun j => rescale (P j) (Q : ℤ)) x (y : ℤ) i ∈ A) ∧
    Function.Injective (pattern (fun j => rescale (P j) (Q : ℤ)) x (y : ℤ))

/-- Absence removes every prime contribution with distinct offsets. -/
theorem sparse_prime_term_eq_zero {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (Q : ℕ) (γ : ℝ) (A : Finset ℤ)
    (hno : NoRescaledConfiguration P Q (1 / γ) A)
    (x : ℤ) (hx : x ∈ A) (y : ℕ) (hy : 1 ≤ y)
    (hprime : (Q * y + 1).Prime)
    (hdist : Function.Injective
      (pattern (fun j => rescale (P j) (Q : ℤ)) x (y : ℤ))) :
    sparseMangoldt γ (Q * y + 1) *
      patternIndicator (fun j => rescale (P j) (Q : ℤ)) A x (y : ℤ) = 0 := by
  by_cases hs : IsPSPrime (1 / γ) (Q * y + 1)
  · have hpat : patternIndicator (fun j => rescale (P j) (Q : ℤ)) A x (y : ℤ) = 0 := by
      by_contra hne
      have hall := (patternIndicator_ne_zero_iff _ A x (y : ℤ)).mp hne
      apply hno
      refine ⟨x, y, hy, hs, ?_, hdist⟩
      intro i
      cases i using Fin.cases with
      | zero => exact hx
      | succ i => exact hall i
    rw [hpat, mul_zero]
  · rw [sparseMangoldt_prime γ hprime, if_neg hs, zero_mul]

/-- Translating all offsets preserves exactly their pairwise distinctness. -/
theorem pattern_injective_iff {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (x y : ℤ) :
    Function.Injective (pattern P x y) ↔
      Function.Injective (fun i : Fin (ℓ + 1) => (recurrencePolynomials P i).eval y) := by
  have hid (i : Fin (ℓ + 1)) : pattern P x y i =
      x + (recurrencePolynomials P i).eval y := by
    cases i using Fin.cases <;> simp [pattern, recurrencePolynomials]
  constructor
  · intro hinj i j hij
    apply hinj
    rw [hid, hid]
    exact congrArg (fun t : ℤ => x + t) hij
  · intro hinj i j hij
    apply hinj
    rw [hid, hid] at hij
    exact add_left_cancel hij

def badParameters {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (Q M : ℕ) : Finset ℕ :=
  (initialInterval M).filter (fun y =>
    ¬Function.Injective (fun i : Fin (ℓ + 1) =>
      (recurrencePolynomials (fun j => rescale (P j) (Q : ℤ)) i).eval (y : ℤ)))

/-- The original polynomial root bound applies to the actual natural-number parameters. -/
theorem card_badParameters_le {ℓ d : ℕ} (P : PolynomialFamily ℓ)
    (Q M : ℕ) (hQ : 1 ≤ Q) (hdeg : ∀ i, (P.polynomials i).natDegree ≤ d) :
    (badParameters P.polynomials Q M).card ≤ d * (ℓ + 1).choose 2 := by
  have hq : (Q : ℤ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  let R : Fin (ℓ + 1) → Polynomial ℤ :=
    Fin.cons (0 : Polynomial ℤ) (fun j => rescale (P.polynomials j) (Q : ℤ))
  have hsub : (badParameters P.polynomials Q M).image (fun y : ℕ => (y : ℤ)) ⊆
      collisionParameters R (Finset.Icc 1 (M : ℤ)) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hyM, hybad⟩ := Finset.mem_filter.mp hy
    apply (mem_collisionParameters_iff R _ _).mpr
    refine ⟨?_, hybad⟩
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_Icc.mp hyM
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hy₁, by exact_mod_cast hy₂⟩
  calc
    (badParameters P.polynomials Q M).card =
        ((badParameters P.polynomials Q M).image (fun y : ℕ => (y : ℤ))).card :=
      (Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)).symm
    _ ≤ (collisionParameters R (Finset.Icc 1 (M : ℤ))).card := Finset.card_le_card hsub
    _ ≤ d * (ℓ + 1).choose 2 := card_rescaled_collisions_le P (Q : ℤ) hq hdeg _

/-- A nonnegative sum along an injective map into a finite set is bounded by its full mass. -/
theorem sum_injective_selected_le {s t : Finset ℕ} (f : ℕ → ℕ)
    (hf : Function.Injective f) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑ y ∈ s.filter (fun y => f y ∈ t), w (f y)) ≤ ∑ n ∈ t, w n := by
  rw [← Finset.sum_image (fun y _ z _ hyz => hf hyz)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp hy).2
  · intro n hn hnot
    exact hw n

theorem sparseMangoldt_vanishes (γ : ℝ) {n : ℕ} (hn : ¬IsPrimePow n) :
    sparseMangoldt γ n = 0 := by
  have hΛ := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  simp [sparseMangoldt, hΛ]

/-- All surviving sparse terms are covered by the actual collision parameters
and by the actual higher prime powers in [1,QM+1]. -/
theorem sparse_term_le_exceptional {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (Q M : ℕ) (γ : ℝ) (hγ : 0 < γ) (A : Finset ℤ)
    (hno : NoRescaledConfiguration P Q (1 / γ) A)
    (x : ℤ) (hx : x ∈ A) (y : ℕ) (hy : y ∈ initialInterval M)
    {B : ℝ} (_hB : 0 ≤ B)
    (hw : sparseMangoldt γ (Q * y + 1) ≤ B) :
    sparseMangoldt γ (Q * y + 1) *
        patternIndicator (fun j => rescale (P j) (Q : ℤ)) A x (y : ℤ) ≤
      (if y ∈ badParameters P Q M then B else 0) +
      (if Q * y + 1 ∈ higherPrimePowers (Q * M + 1) then
        sparseMangoldt γ (Q * y + 1) else 0) := by
  have hweight : 0 ≤ sparseMangoldt γ (Q * y + 1) := sparseMangoldt_nonneg hγ _
  have hterm : sparseMangoldt γ (Q * y + 1) *
      patternIndicator (fun j => rescale (P j) (Q : ℤ)) A x (y : ℤ) ≤
      sparseMangoldt γ (Q * y + 1) := by
    simpa using mul_le_mul_of_nonneg_left
      (patternIndicator_le_one (fun j => rescale (P j) (Q : ℤ)) A x (y : ℤ)) hweight
  have hsecond : 0 ≤ (if Q * y + 1 ∈ higherPrimePowers (Q * M + 1) then
      sparseMangoldt γ (Q * y + 1) else 0) := by split_ifs <;> positivity
  by_cases hbad : y ∈ badParameters P Q M
  · rw [if_pos hbad]
    exact (hterm.trans hw).trans (le_add_of_nonneg_right hsecond)
  · rw [if_neg hbad, zero_add]
    have hdist : Function.Injective
        (pattern (fun j => rescale (P j) (Q : ℤ)) x (y : ℤ)) := by
      apply (pattern_injective_iff _ x (y : ℤ)).mpr
      have := not_and.mp (show ¬(y ∈ initialInterval M ∧
        ¬Function.Injective (fun i : Fin (ℓ + 1) =>
          (recurrencePolynomials (fun j => rescale (P j) (Q : ℤ)) i).eval (y : ℤ))) by
            simpa only [badParameters, Finset.mem_filter] using hbad)
      exact Classical.not_not.mp (this hy)
    by_cases hp : (Q * y + 1).Prime
    · rw [sparse_prime_term_eq_zero P Q γ A hno x hx y (Finset.mem_Icc.mp hy).1 hp hdist]
      exact hsecond
    · by_cases hpow : IsPrimePow (Q * y + 1)
      · have hn : Q * y + 1 ∈ higherPrimePowers (Q * M + 1) := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hpow, hp⟩
          exact Nat.add_le_add_right (Nat.mul_le_mul_left Q (Finset.mem_Icc.mp hy).2) 1
        rw [if_pos hn]
        exact hterm
      · rw [sparseMangoldt_vanishes γ hpow, zero_mul]
        split_ifs <;> simp

/-- A fixed spatial point incurs only the collision envelope and global
higher-prime-power mass. The progression parameter map is proved injective. -/
theorem sparse_parameter_sum_le {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (Q M : ℕ) (hQ : 1 ≤ Q) (γ : ℝ) (hγ : 0 < γ) (A : Finset ℤ)
    (hno : NoRescaledConfiguration P Q (1 / γ) A)
    (x : ℤ) (hx : x ∈ A) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ y ∈ initialInterval M, sparseMangoldt γ (Q * y + 1) ≤ B) :
    (∑ y ∈ initialInterval M, sparseMangoldt γ (Q * y + 1) *
      patternIndicator (fun j => rescale (P j) (Q : ℤ)) A x (y : ℤ)) ≤
      ((badParameters P Q M).card : ℝ) * B +
        ∑ n ∈ higherPrimePowers (Q * M + 1),
          (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n) := by
  have hb : (∑ y ∈ initialInterval M, (if y ∈ badParameters P Q M then B else 0)) =
      ((badParameters P Q M).card : ℝ) * B := by
    rw [← Finset.sum_filter]
    have heq : (initialInterval M).filter (fun y => y ∈ badParameters P Q M) =
        badParameters P Q M := by
      ext y
      simp [badParameters, and_assoc, and_left_comm, and_comm]
    rw [heq]
    simp
  have hf : Function.Injective (fun y : ℕ => Q * y + 1) := by
    intro y z heq
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < Q) (Nat.add_right_cancel heq)
  have hp : (∑ y ∈ initialInterval M,
      (if Q * y + 1 ∈ higherPrimePowers (Q * M + 1) then
        sparseMangoldt γ (Q * y + 1) else 0)) ≤
      ∑ n ∈ higherPrimePowers (Q * M + 1), sparseMangoldt γ n := by
    simpa only [Finset.sum_filter] using
      (sum_injective_selected_le (s := initialInterval M)
        (t := higherPrimePowers (Q * M + 1)) (fun y => Q * y + 1) hf
        (sparseMangoldt γ) (fun n => sparseMangoldt_nonneg hγ n))
  calc
    _ ≤ ∑ y ∈ initialInterval M,
        ((if y ∈ badParameters P Q M then B else 0) +
          (if Q * y + 1 ∈ higherPrimePowers (Q * M + 1) then
            sparseMangoldt γ (Q * y + 1) else 0)) :=
      Finset.sum_le_sum (fun y hy => sparse_term_le_exceptional P Q M γ hγ A hno x hx y hy hB (hw y hy))
    _ = _ := by rw [Finset.sum_add_distrib, hb]
    _ ≤ ((badParameters P Q M).card : ℝ) * B +
        ∑ n ∈ higherPrimePowers (Q * M + 1), sparseMangoldt γ n := add_le_add_left hp _
    _ ≤ _ := by
      apply add_le_add_left
      exact Finset.sum_le_sum (fun n _ => le_add_of_nonneg_right ArithmeticFunction.vonMangoldt_nonneg)

/-- Actual sparse set count under the forbidden-configuration hypothesis.
The conclusion retains explicit, proved collision and higher-power errors. -/
theorem sparse_setCountingForm_le_exceptional {ℓ d : ℕ} (P : PolynomialFamily ℓ)
    (N Q M : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hdeg : ∀ i, (P.polynomials i).natDegree ≤ d)
    (γ : ℝ) (hγ : 0 < γ) (A : Finset ℤ) (hA : A.card ≤ N)
    (hno : NoRescaledConfiguration P.polynomials Q (1 / γ) A)
    {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ y ∈ initialInterval M, sparseMangoldt γ (Q * y + 1) ≤ B) :
    setCountingForm N M Q (fun j => rescale (P.polynomials j) (Q : ℤ))
      (sparseMangoldt γ) A ≤
        ((d * (ℓ + 1).choose 2 : ℕ) * B +
          ∑ n ∈ higherPrimePowers (Q * M + 1),
            (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n)) / (M : ℝ) := by
  let E : ℝ := (d * (ℓ + 1).choose 2 : ℕ) * B +
    ∑ n ∈ higherPrimePowers (Q * M + 1),
      (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n)
  have hE : 0 ≤ E := by
    apply add_nonneg (mul_nonneg (Nat.cast_nonneg _) hB)
    exact Finset.sum_nonneg (fun n _ => add_nonneg
      (sparseMangoldt_nonneg hγ n) ArithmeticFunction.vonMangoldt_nonneg)
  have hxbound (x : ℤ) (hx : x ∈ A) :
      (∑ y ∈ initialInterval M, sparseMangoldt γ (Q * y + 1) *
        patternIndicator (fun j => rescale (P.polynomials j) (Q : ℤ)) A x (y : ℤ)) ≤ E := by
    apply (sparse_parameter_sum_le P.polynomials Q M hQ γ hγ A hno x hx hB hw).trans
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_badParameters_le P Q M hQ hdeg) hB
  have hsum : (∑ x ∈ A, ∑ y ∈ initialInterval M, sparseMangoldt γ (Q * y + 1) *
        patternIndicator (fun j => rescale (P.polynomials j) (Q : ℤ)) A x (y : ℤ)) ≤ (N : ℝ) * E := by
    calc
      _ ≤ ∑ _x ∈ A, E := Finset.sum_le_sum hxbound
      _ = (A.card : ℝ) * E := by simp
      _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_right (by exact_mod_cast hA) hE
  change ((N : ℝ) * (M : ℝ))⁻¹ * _ ≤ E / (M : ℝ)
  apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))).trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  field_simp
  ring

/-- Explicit elementary error before applying the degree-uniform comparison. -/
def sparseCountError (γ : ℝ) (d ℓ Q M : ℕ) : ℝ :=
  (((d * (ℓ + 1).choose 2 : ℕ) : ℝ) *
      (γ⁻¹ * ((Q * M + 1 : ℕ) : ℝ) ^ (1 - γ) * Real.log ((Q * M + 1 : ℕ) : ℝ)) +
    ((γ⁻¹ + 1) / Real.log 2) * ((Q * M + 1 : ℕ) : ℝ) ^ (3 / 2 - γ) *
      (Real.log ((Q * M + 1 : ℕ) : ℝ)) ^ 2) / (M : ℝ)

/-- The actual sparse count satisfies the explicit elementary error estimate. -/
theorem sparse_setCountingForm_le_error {ℓ d : ℕ} (P : PolynomialFamily ℓ)
    (N Q M : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hdeg : ∀ i, (P.polynomials i).natDegree ≤ d)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (A : Finset ℤ) (hA : A.card ≤ N)
    (hno : NoRescaledConfiguration P.polynomials Q (1 / γ) A) :
    setCountingForm N M Q (fun j => rescale (P.polynomials j) (Q : ℤ))
      (sparseMangoldt γ) A ≤ sparseCountError γ d ℓ Q M := by
  let B : ℝ := γ⁻¹ * ((Q * M + 1 : ℕ) : ℝ) ^ (1 - γ) * Real.log ((Q * M + 1 : ℕ) : ℝ)
  have hB : 0 ≤ B := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.log_natCast_nonneg _)
  apply (sparse_setCountingForm_le_exceptional P N Q M hN hQ hM hdeg γ hγ A hA hno hB ?_).trans
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
    apply add_le_add_left
    exact higherPrimePowers_combined_mass_rpow_le hγ hγ₁ (Q * M + 1)
  · intro y hy
    dsimp only [B]
    apply sparseMangoldt_le_envelope hγ hγ₁
    · omega
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left Q (Finset.mem_Icc.mp hy).2) 1

/-- Linearity of the actual real counting form, with the exact discrepancy sign. -/
theorem setCountingForm_discrepancy {ℓ : ℕ} (N M Q : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (γ : ℝ) (A : Finset ℤ) :
    setCountingForm N M Q P (discrepancyWeight γ) A =
      setCountingForm N M Q P (sparseMangoldt γ) A -
      setCountingForm N M Q P ArithmeticFunction.vonMangoldt A := by
  simp only [setCountingForm, discrepancyWeight, sub_mul, Finset.sum_sub_distrib, mul_sub]

/-- The checked complex analytic comparison controls precisely the real set-count error. -/
theorem abs_setCountingForm_discrepancy_le {ℓ : ℕ} (N M Q : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (γ E : ℝ) (A : Finset ℤ)
    (hcompare : ‖countingForm N M Q P (fun n => (discrepancyWeight γ n : ℂ))
      (indicatorFinsupp A) (fun _ x => (setIndicator A x : ℂ))‖ ≤ E) :
    |setCountingForm N M Q P (sparseMangoldt γ) A -
      setCountingForm N M Q P ArithmeticFunction.vonMangoldt A| ≤ E := by
  rw [← setCountingForm_eq_countingForm] at hcompare
  simpa only [Complex.norm_real, Real.norm_eq_abs, setCountingForm_discrepancy] using hcompare

/-- No-configuration plus a genuine analytic comparison bounds the ordinary-prime count. -/
theorem ordinary_setCountingForm_le_error {ℓ d : ℕ} (P : PolynomialFamily ℓ)
    (N Q M : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hdeg : ∀ i, (P.polynomials i).natDegree ≤ d)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (A : Finset ℤ) (hA : A.card ≤ N)
    (hno : NoRescaledConfiguration P.polynomials Q (1 / γ) A) (E : ℝ)
    (hcompare : ‖countingForm N M Q (fun j => rescale (P.polynomials j) (Q : ℤ))
      (fun n => (discrepancyWeight γ n : ℂ))
      (indicatorFinsupp A) (fun _ x => (setIndicator A x : ℂ))‖ ≤ E) :
    setCountingForm N M Q (fun j => rescale (P.polynomials j) (Q : ℤ))
      ArithmeticFunction.vonMangoldt A ≤ sparseCountError γ d ℓ Q M + E := by
  have hs := sparse_setCountingForm_le_error P N Q M hN hQ hM hdeg γ hγ hγ₁ A hA hno
  have hc := abs_setCountingForm_discrepancy_le N M Q
    (fun j => rescale (P.polynomials j) (Q : ℤ)) γ E A hcompare
  have hside := (abs_le.mp hc).1
  linarith

/-- The full-factor KMTT real count and the f₀-supported set count agree exactly. -/
theorem realSetCount_eq_setCountingForm {ℓ : ℕ} (N M Q : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (w : ℕ → ℝ) (A : Finset ℤ)
    (hA : A ⊆ integerInterval N) :
    realSetCount N M Q P w A = setCountingForm N M Q P w A := by
  have hprod (x y : ℤ) :
      (∏ i : Fin (ℓ + 1), realIndicator A 1 (x + (recurrencePolynomials P i).eval y)) =
        setIndicator A x * patternIndicator P A x y := by
    simp [Fin.prod_univ_succ, recurrencePolynomials, realIndicator, setIndicator, patternIndicator]
  have hsum (y : ℕ) : (∑ x ∈ integerInterval N,
      w (Q * y + 1) * (setIndicator A x * patternIndicator P A x (y : ℤ))) =
      ∑ x ∈ A, w (Q * y + 1) * patternIndicator P A x (y : ℤ) := by
    calc
      _ = ∑ x ∈ A, w (Q * y + 1) * (setIndicator A x * patternIndicator P A x (y : ℤ)) := by
        symm
        apply Finset.sum_subset hA
        intro x hx hxA
        simp [setIndicator_of_not_mem hxA]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [setIndicator_of_mem hx]
  unfold realSetCount realConfigurationForm setCountingForm
  simp_rw [hprod]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y _ => hsum y)

/-- Scalar model inputs factor out with exactly ℓ+1 copies of the density. -/
theorem realModelCount_eq_mul_realSetCount {ℓ : ℕ} (N M Q : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (w : ℕ → ℝ) (δ : ℝ) :
    realModelCount N M Q P w δ =
      δ ^ (ℓ + 1) * realSetCount N M Q P w (integerInterval N) := by
  have hI (x : ℤ) : realIndicator (integerInterval N) δ x =
      δ * realIndicator (integerInterval N) 1 x := by
    unfold realIndicator
    split_ifs <;> simp
  have hterm (x : ℤ) (y : ℕ) :
      w (Q * y + 1) * (∏ i : Fin (ℓ + 1),
        realIndicator (integerInterval N) δ (x + (recurrencePolynomials P i).eval (y : ℤ))) =
      δ ^ (ℓ + 1) * (w (Q * y + 1) * (∏ i : Fin (ℓ + 1),
        realIndicator (integerInterval N) 1 (x + (recurrencePolynomials P i).eval (y : ℤ)))) := by
    simp_rw [hI, Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  unfold realModelCount realSetCount realConfigurationForm
  simp_rw [hterm, ← Finset.mul_sum]
  ring

theorem realModelCount_eq_density_mul_setCountingForm {ℓ : ℕ} (N M Q : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (w : ℕ → ℝ) (δ : ℝ) :
    realModelCount N M Q P w δ =
      δ ^ (ℓ + 1) * setCountingForm N M Q P w (integerInterval N) := by
  rw [realModelCount_eq_mul_realSetCount,
    realSetCount_eq_setCountingForm N M Q P w (integerInterval N) (Finset.Subset.refl _)]

theorem patternIndicator_eq_ite {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (A : Finset ℤ) (x y : ℤ) :
    patternIndicator P A x y = if (∀ i, x + (P i).eval y ∈ A) then 1 else 0 := by
  by_cases h : ∀ i, x + (P i).eval y ∈ A
  · rw [if_pos h, patternIndicator_eq_one P A x y h]
  · rw [if_neg h]
    by_contra hne
    exact h ((patternIndicator_ne_zero_iff P A x y).mp hne)

/-- The finite reference count counts exactly the common translated interval. -/
theorem sum_patternIndicator_interval {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (N : ℕ) (y : ℤ) :
    (∑ x ∈ integerInterval N, patternIndicator P (integerInterval N) x y) =
      ((translatedIntervalIntersection N (fun i => (P i).eval y)).card : ℝ) := by
  simp_rw [patternIndicator_eq_ite]
  rw [← Finset.sum_filter]
  simp only [translatedIntervalIntersection, integerInterval, Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-- Nonnegative weights and small shifts give the precise truncated model lower bound. -/
theorem modelCountingForm_lower_of_small_shifts {ℓ : ℕ} (N M Q K : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hKM : K ≤ M)
    (P : Fin ℓ → Polynomial ℤ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hshift : ∀ y ∈ initialInterval K, ∀ i, |(((P i).eval (y : ℤ) : ℤ) : ℝ)| ≤ (N : ℝ) / 10) :
    δ ^ (ℓ + 1) / (2 * (M : ℝ)) * (∑ y ∈ initialInterval K, w (Q * y + 1)) ≤
      realModelCount N M Q P w δ := by
  have hoverlap (y : ℕ) (hy : y ∈ initialInterval K) :
      (N : ℝ) / 2 ≤ ∑ x ∈ integerInterval N, patternIndicator P (integerInterval N) x (y : ℤ) := by
    rw [sum_patternIndicator_interval]
    exact card_translatedIntervalIntersection_ge_half N (by omega)
      (fun i => (P i).eval (y : ℤ)) (hshift y hy)
  have hnum : (N : ℝ) / 2 * (∑ y ∈ initialInterval K, w (Q * y + 1)) ≤
      ∑ x ∈ integerInterval N, ∑ y ∈ initialInterval M,
        w (Q * y + 1) * patternIndicator P (integerInterval N) x (y : ℤ) := by
    calc
      _ = ∑ y ∈ initialInterval K, w (Q * y + 1) * ((N : ℝ) / 2) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ ∑ y ∈ initialInterval K, w (Q * y + 1) *
          (∑ x ∈ integerInterval N, patternIndicator P (integerInterval N) x (y : ℤ)) :=
        Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hoverlap y hy) (hw _))
      _ ≤ ∑ y ∈ initialInterval M, w (Q * y + 1) *
          (∑ x ∈ integerInterval N, patternIndicator P (integerInterval N) x (y : ℤ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro y hy
          obtain ⟨hy₁, hy₂⟩ := Finset.mem_Icc.mp hy
          exact Finset.mem_Icc.mpr ⟨hy₁, hy₂.trans hKM⟩
        · intro y hy hnot
          exact mul_nonneg (hw _) (Finset.sum_nonneg (fun x _ =>
            patternIndicator_nonneg P (integerInterval N) x (y : ℤ)))
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
  rw [realModelCount_eq_density_mul_setCountingForm]
  unfold setCountingForm
  have hcoef : 0 ≤ δ ^ (ℓ + 1) * ((N : ℝ) * (M : ℝ))⁻¹ := by positivity
  have hbound := mul_le_mul_of_nonneg_left hnum hcoef
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  convert hbound using 1 <;> field_simp <;> ring

/-- The source-compatible mass witness and the elementary coefficient cutoff
establish the model lower bound for every actual rescaled family. -/
theorem modelCountingForm_lower_of_primeMassWitness {ℓ d Adiv : ℕ}
    (p : KMTTComparisonParameters ℓ Adiv) (P : PolynomialFamily ℓ)
    (C : ℝ) (hC : 1 ≤ C) (hd : 1 ≤ d)
    (hdeg : ∀ i, (P.polynomials i).natDegree ≤ d)
    (hcoeff : ∀ i j, j ≤ d → |(P.polynomials i |>.coeff j : ℝ)| ≤ C)
    (mass : PrimeProgressionMassWitness p d (1 / (10 * C * (d + 1 : ℕ))))
    (N Q s : ℕ) (δ : ℝ) (hN : 1 ≤ N) (hM : 1 ≤ floorScale N Q d)
    (hδ : 0 ≤ δ) (hlarge : mass.threshold ≤ N) (hadmiss : KMTTAdmissible p N Q s δ) :
    (2 * p.c₁) * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) ≤
      realModelCount N (floorScale N Q d) Q
        (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt δ := by
  let M := floorScale N Q d
  let K : ℕ := ⌊mass.cutoff * (M : ℝ)⌋₊
  have hQ : 1 ≤ Q := hadmiss.1
  have hKreal : (K : ℝ) ≤ mass.cutoff * (M : ℝ) :=
    Nat.floor_le (mul_nonneg mass.cutoff_pos.le (Nat.cast_nonneg _))
  have hKM : K ≤ M := by
    have : (K : ℝ) ≤ M := hKreal.trans (by
      simpa using mul_le_mul_of_nonneg_right mass.cutoff_le_one (Nat.cast_nonneg M))
    exact_mod_cast this
  have hshift : ∀ y ∈ initialInterval K, ∀ i,
      |(((rescale (P.polynomials i) (Q : ℤ)).eval (y : ℤ) : ℤ) : ℝ)| ≤ (N : ℝ) / 10 := by
    intro y hy i
    apply abs_eval_rescale_le_tenth_floorScale (P.polynomials i) Q N d (y : ℤ) C hQ hd hM
    · exact_mod_cast (Nat.zero_le y)
    · exact hC
    · exact hdeg i
    · exact hcoeff i
    · have hyK : (y : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hy).2
      have hcut := mul_le_mul_of_nonneg_right mass.cutoff_le (Nat.cast_nonneg M)
      exact hyK.trans (hKreal.trans hcut)
  have hmodel := modelCountingForm_lower_of_small_shifts N M Q K hN hM hKM
    (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg) δ hδ hshift
  have hmass := mass.truncated_mass N Q s δ hlarge hadmiss
  have hfactor : 0 ≤ δ ^ (ℓ + 1) / (2 * (M : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmass hfactor
  apply le_trans ?_ hmodel
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  convert hscaled using 1 <;> simp only [primeProgressionMass] <;> field_simp <;> ring

/-- Finite form of Lemma 3.2 with a single explicit remaining error inequality.
Every count in the conclusion is the actual manuscript counting form, and
absence, collisions, higher prime powers, comparison and model overlap have
all been connected by proved lemmas. Uniform asymptotic error dominance is
not assumed to be proved by this finite theorem. -/
theorem prime_discrepancy_finite {ℓ d Adiv : ℕ}
    (p : KMTTComparisonParameters ℓ Adiv) (P : PolynomialFamily ℓ)
    (C : ℝ) (hC : 1 ≤ C) (hd : 1 ≤ d)
    (hdeg : ∀ i, (P.polynomials i).natDegree ≤ d)
    (hcoeff : ∀ i j, j ≤ d → |(P.polynomials i |>.coeff j : ℝ)| ≤ C)
    (mass : PrimeProgressionMassWitness p d (1 / (10 * C * (d + 1 : ℕ))))
    (N Q s : ℕ) (δ γ E : ℝ) (hN : 1 ≤ N) (hM : 1 ≤ floorScale N Q d)
    (hδ : 0 ≤ δ) (hγ : 0 < γ) (hγ₁ : γ ≤ 1)
    (hlarge : mass.threshold ≤ N) (hadmiss : KMTTAdmissible p N Q s δ)
    (A : Finset ℤ) (hA : A ⊆ integerInterval N)
    (hno : NoRescaledConfiguration P.polynomials Q (1 / γ) A)
    (hcompare : ‖countingForm N (floorScale N Q d) Q
      (fun j => rescale (P.polynomials j) (Q : ℤ))
      (fun n => (discrepancyWeight γ n : ℂ))
      (indicatorFinsupp A) (fun _ x => (setIndicator A x : ℂ))‖ ≤ E)
    (herror : sparseCountError γ d ℓ Q (floorScale N Q d) + E ≤
      p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d)) :
    p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) ≤
      |realSetCount N (floorScale N Q d) Q
        (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt A -
       realModelCount N (floorScale N Q d) Q
        (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt δ| := by
  have hQ : 1 ≤ Q := hadmiss.1
  have hcard : A.card ≤ N := (Finset.card_le_card hA).trans_eq (card_integerInterval N)
  have hcount := ordinary_setCountingForm_le_error P N Q (floorScale N Q d) hN hQ hM
    hdeg γ hγ hγ₁ A hcard hno E hcompare
  have hmodel := modelCountingForm_lower_of_primeMassWitness p P C hC hd hdeg hcoeff
    mass N Q s δ hN hM hδ hlarge hadmiss
  rw [realSetCount_eq_setCountingForm N (floorScale N Q d) Q _ _ A hA]
  apply le_trans ?_ (neg_le_abs _)
  nlinarith

end PSPrimes
