import PSPrimes.Definitions

/-!
# Polynomial shifts and finite orbit support

The spatial transference of the finite von Neumann estimate uses the
polynomials `P_i(n-1)`. These exact identities and bounds keep its support
constant independent of the cutoff and the probability system.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- The integer polynomial whose value at `n` is `P(n-1)`. -/
def shiftedOrbitPolynomial (P : Polynomial ℤ) : Polynomial ℤ :=
  P.comp (Polynomial.X - Polynomial.C 1)

@[simp] theorem eval_shiftedOrbitPolynomial (P : Polynomial ℤ) (n : ℤ) :
    (shiftedOrbitPolynomial P).eval n = P.eval (n - 1) := by
  simp [shiftedOrbitPolynomial, Polynomial.eval_comp]

@[simp] theorem natDegree_shiftedOrbitPolynomial (P : Polynomial ℤ) :
    (shiftedOrbitPolynomial P).natDegree = P.natDegree := by
  rw [shiftedOrbitPolynomial, Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]

theorem strictMono_shiftedOrbitPolynomial {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : StrictMono (fun i => (P i).natDegree)) :
    StrictMono (fun i => (shiftedOrbitPolynomial (P i)).natDegree) := by
  simpa only [natDegree_shiftedOrbitPolynomial] using hP

/-- A single fixed support constant, including arbitrary constant terms. -/
def orbitSupportConstant {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (d : ℕ) : ℝ :=
  1 + ∑ i, ∑ j ∈ Finset.range (d + 1), |((P i).coeff j : ℝ)|

theorem one_le_orbitSupportConstant {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (d : ℕ) :
    1 ≤ orbitSupportConstant P d := by
  unfold orbitSupportConstant
  have h : 0 ≤ ∑ i, ∑ j ∈ Finset.range (d + 1), |((P i).coeff j : ℝ)| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  linarith

/-- Fixed-degree evaluation bound on the whole interval `[0,N]`. -/
theorem abs_eval_le_coefficient_sum (P : Polynomial ℤ) (d N : ℕ) (y : ℤ)
    (hdeg : P.natDegree ≤ d) (hN : 1 ≤ N) (hy : 0 ≤ y) (hyN : y ≤ N) :
    |((P.eval y : ℤ) : ℝ)| ≤
      (∑ j ∈ Finset.range (d + 1), |(P.coeff j : ℝ)|) * (N : ℝ) ^ d := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hyr : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hyNr : (y : ℝ) ≤ N := by exact_mod_cast hyN
  have heval : ((P.eval y : ℤ) : ℝ) =
      ∑ j ∈ Finset.range (d + 1), (P.coeff j : ℝ) * (y : ℝ) ^ j := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg (Nat.lt_succ_self d))]
    push_cast
    rfl
  rw [heval, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [abs_mul, abs_pow, abs_of_nonneg hyr]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (pow_le_pow_left₀ hyr hyNr j).trans (pow_le_pow_right₀ hNr hjd)

theorem orbit_spatial_support_bound {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (d N : ℕ) (hN : 1 ≤ N) (a : ℤ) (ha : a ∈ Finset.Icc 1 ((N : ℤ) ^ d)) :
    |(a : ℝ)| ≤ orbitSupportConstant P d * (N : ℝ) ^ d := by
  have har : (0 : ℝ) ≤ a := by
    have ha' := (Finset.mem_Icc.mp ha).1
    exact_mod_cast (show (0 : ℤ) ≤ a by omega)
  have haN : (a : ℝ) ≤ (N : ℝ) ^ d := by
    exact_mod_cast (Finset.mem_Icc.mp ha).2
  rw [abs_of_nonneg har]
  calc
    (a : ℝ) ≤ (N : ℝ) ^ d := haN
    _ ≤ orbitSupportConstant P d * (N : ℝ) ^ d := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_orbitSupportConstant P d) (by positivity : 0 ≤ (N : ℝ) ^ d)

/-- All translated orbit samples lie in one fixed multiple of `[-N^d,N^d]`.
The constant is fixed before `N`, the system, or any input function. -/
theorem orbit_shift_support_bound {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (d : ℕ) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (N : ℕ) (hN : 1 ≤ N) (a : ℤ) (ha : a ∈ Finset.Icc 1 ((N : ℤ) ^ d))
    (n : ℕ) (hn : n ∈ initialInterval N) (i : Fin ℓ) :
    |((a + (P i).eval ((n : ℤ) - 1) : ℤ) : ℝ)| ≤
      orbitSupportConstant P d * (N : ℝ) ^ d := by
  classical
  have hn' := Finset.mem_Icc.mp hn
  have hy : (0 : ℤ) ≤ (n : ℤ) - 1 := by omega
  have hyN : (n : ℤ) - 1 ≤ N := by omega
  have heval := abs_eval_le_coefficient_sum (P i) d N ((n : ℤ) - 1)
    (hdeg i) hN hy hyN
  have ha' := Finset.mem_Icc.mp ha
  have har : (0 : ℝ) ≤ a := by exact_mod_cast (show (0 : ℤ) ≤ a by omega)
  have haN : (a : ℝ) ≤ (N : ℝ) ^ d := by exact_mod_cast ha'.2
  have hi : (∑ j ∈ Finset.range (d + 1), |((P i).coeff j : ℝ)|) ≤
      ∑ i, ∑ j ∈ Finset.range (d + 1), |((P i).coeff j : ℝ)| :=
    Finset.single_le_sum
      (f := fun i : Fin ℓ => ∑ j ∈ Finset.range (d + 1), |((P i).coeff j : ℝ)|)
      (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  push_cast
  calc
    |(a : ℝ) + (((P i).eval ((n : ℤ) - 1) : ℤ) : ℝ)| ≤
        |(a : ℝ)| + |(((P i).eval ((n : ℤ) - 1) : ℤ) : ℝ)| := abs_add_le _ _
    _ ≤ (N : ℝ) ^ d +
        (∑ j ∈ Finset.range (d + 1), |((P i).coeff j : ℝ)|) * (N : ℝ) ^ d := by
      exact add_le_add (by simpa only [abs_of_nonneg har] using haN) heval
    _ ≤ (N : ℝ) ^ d +
        (∑ i, ∑ j ∈ Finset.range (d + 1), |((P i).coeff j : ℝ)|) * (N : ℝ) ^ d :=
      add_le_add_left (mul_le_mul_of_nonneg_right hi (by positivity)) _
    _ = orbitSupportConstant P d * (N : ℝ) ^ d := by
      unfold orbitSupportConstant
      ring

end PSPrimes
