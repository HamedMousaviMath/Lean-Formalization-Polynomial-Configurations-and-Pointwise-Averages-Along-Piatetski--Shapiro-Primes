import PSPrimes.RecurrenceDefinitions
import PSPrimes.Rescaling

noncomputable section
namespace PSPrimes

def familyCoefficientBound {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) : ℝ :=
  1 + ∑ i, ∑ j ∈ (P i).support, (|((P i).coeff j)| : ℝ)

theorem one_le_familyCoefficientBound {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) :
    1 ≤ familyCoefficientBound P := by
  unfold familyCoefficientBound
  have hs : 0 ≤ ∑ i, ∑ j ∈ (P i).support, (|((P i).coeff j)| : ℝ) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
  linarith

theorem coefficient_le_familyCoefficientBound {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (i : Fin ℓ) (j : ℕ) : (|((P i).coeff j)| : ℝ) ≤ familyCoefficientBound P := by
  classical
  have htotal : (∑ k ∈ (P i).support, (|((P i).coeff k)| : ℝ)) ≤
      ∑ i, ∑ k ∈ (P i).support, (|((P i).coeff k)| : ℝ) :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin ℓ => ∑ k ∈ (P i).support, (|((P i).coeff k)| : ℝ))
      (fun (i : Fin ℓ) _ => Finset.sum_nonneg
      (fun (k : ℕ) _ => (by positivity : (0 : ℝ) ≤ (|((P i).coeff k)| : ℝ))))
      (Finset.mem_univ i)
  by_cases hj : j ∈ (P i).support
  · have hsingle : (|((P i).coeff j)| : ℝ) ≤
        ∑ k ∈ (P i).support, (|((P i).coeff k)| : ℝ) :=
      Finset.single_le_sum (f := fun k : ℕ => (|((P i).coeff k)| : ℝ))
        (fun k _ => by positivity) hj
    unfold familyCoefficientBound
    linarith
  · have hz : (P i).coeff j = 0 := Polynomial.not_mem_support_iff.mp hj
    simp only [hz, abs_zero, Int.cast_zero]
    exact le_trans (by norm_num) (one_le_familyCoefficientBound P)

def PolynomialFamily.rescaled {ℓ : ℕ} (P : PolynomialFamily ℓ)
    (Q : ℕ) (hQ : 0 < Q) : PolynomialFamily ℓ where
  polynomials := fun i => rescale (P.polynomials i) (Q : ℤ)
  nonempty := P.nonempty
  zero_constant := fun _ => coeff_rescale_zero _ _
  positive_degree := by
    intro i
    rw [natDegree_rescale _ _ (by exact_mod_cast (Nat.ne_of_gt hQ)) (by have := P.positive_degree i; omega)]
    exact P.positive_degree i
  increasing_degrees := by
    intro i j hij
    change (rescale (P.polynomials i) (Q : ℤ)).natDegree <
      (rescale (P.polynomials j) (Q : ℤ)).natDegree
    rw [natDegree_rescale _ _ (by exact_mod_cast (Nat.ne_of_gt hQ)) (by have := P.positive_degree i; omega),
      natDegree_rescale _ _ (by exact_mod_cast (Nat.ne_of_gt hQ)) (by have := P.positive_degree j; omega)]
    exact P.increasing_degrees hij

@[simp] theorem PolynomialFamily.natDegree_rescaled {ℓ : ℕ} (P : PolynomialFamily ℓ)
    (Q : ℕ) (hQ : 0 < Q) (i : Fin ℓ) :
    ((P.rescaled Q hQ).polynomials i).natDegree = (P.polynomials i).natDegree := by
  exact natDegree_rescale _ _ (by exact_mod_cast (Nat.ne_of_gt hQ))
    (by have := P.positive_degree i; omega)

/-- The rescaled family has the same `(C,Q)` coefficient bound uniformly in
the modulus; here C is real, as in the external KMTT statements. -/
theorem rescale_hasCQCoefficients (P : Polynomial ℤ) (Q : ℕ) (hQ : 1 ≤ Q)
    (_hP : P.coeff 0 = 0) (hd : 1 ≤ P.natDegree)
    (C : ℝ) (hC : 1 ≤ C) (hb : ∀ j, (|P.coeff j| : ℝ) ≤ C) :
    HasCQCoefficients C Q (rescale P (Q : ℤ)) := by
  have hq : (Q : ℤ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hdeg : 0 < P.natDegree := by omega
  have hdeq := natDegree_rescale P (Q : ℤ) hq hdeg
  have hlead : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hdeg)
  refine ⟨coeff_rescale_zero _ _, ?_, P.coeff P.natDegree, ?_, ?_, hb _, ?_⟩
  · simpa [hdeq] using hd
  · rw [hdeq, coeff_rescale, if_neg (by omega : P.natDegree ≠ 0)]
  · exact abs_pos.mpr hlead
  · intro j hj hjd
    rw [hdeq] at hjd ⊢
    rw [coeff_rescale, coeff_rescale, if_neg (by omega : j ≠ 0),
      if_neg (by omega : P.natDegree ≠ 0)]
    have hqreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hleadreal : (1 : ℝ) ≤ |(P.coeff P.natDegree : ℝ)| := by
      exact_mod_cast Int.one_le_abs hlead
    have hpow : (Q : ℝ) ^ (j - 1) ≤ (Q : ℝ) ^ (P.natDegree - 1) :=
      pow_le_pow_right₀ hqreal (Nat.sub_le_sub_right hjd.le 1)
    push_cast
    simp only [abs_mul, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ (Q : ℝ) from Nat.cast_nonneg Q)]
    calc
      |(P.coeff j : ℝ)| * (Q : ℝ) ^ (j - 1) ≤ C * (Q : ℝ) ^ (j - 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hb j) (by positivity)
      _ ≤ C * (Q : ℝ) ^ (P.natDegree - 1) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      _ ≤ C * (|(P.coeff P.natDegree : ℝ)| * (Q : ℝ) ^ (P.natDegree - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hleadreal (show 0 ≤ (Q : ℝ) ^ (P.natDegree - 1) by positivity)

end PSPrimes
