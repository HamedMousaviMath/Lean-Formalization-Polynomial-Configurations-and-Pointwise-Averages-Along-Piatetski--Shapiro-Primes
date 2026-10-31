import Mathlib

/-!
# Exact integer polynomial rescaling

For a polynomial `P` with zero constant coefficient, `rescale P q` is the
integer polynomial called `P_{i,Q}` in the manuscript.  It is defined
coefficientwise, so neither rational coefficients nor truncated integer division
are hidden in the definition.
-/

namespace PSPrimes

open Polynomial

/-- The coefficientwise integer polynomial `P(qY)/q` when `P(0)=0`. -/
noncomputable def rescale (P : Polynomial ℤ) (q : ℤ) : Polynomial ℤ :=
  P.sum fun n a => monomial n (if n = 0 then 0 else a * q ^ (n - 1))

theorem coeff_rescale (P : Polynomial ℤ) (q : ℤ) (n : ℕ) :
    (rescale P q).coeff n = if n = 0 then 0 else P.coeff n * q ^ (n - 1) := by
  classical
  unfold rescale
  rw [coeff_sum]
  change (∑ b ∈ P.support,
    (monomial b (if b = 0 then 0 else P.coeff b * q ^ (b - 1))).coeff n) = _
  simp_rw [coeff_monomial]
  by_cases hn : n ∈ P.support
  · simp [Finset.sum_ite_eq', hn]
  · have hz : P.coeff n = 0 := not_mem_support_iff.mp hn
    simp [Finset.sum_ite_eq', hn, hz]

@[simp] theorem coeff_rescale_zero (P : Polynomial ℤ) (q : ℤ) :
    (rescale P q).coeff 0 = 0 := by simp [coeff_rescale]

theorem natDegree_rescale_le (P : Polynomial ℤ) (q : ℤ) :
    (rescale P q).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hz := coeff_eq_zero_of_natDegree_lt hn
  simp [coeff_rescale, hz]

/-- Rescaling by a nonzero integer retains the original positive degree. -/
theorem natDegree_rescale (P : Polynomial ℤ) (q : ℤ)
    (hq : q ≠ 0) (hdeg : 0 < P.natDegree) :
    (rescale P q).natDegree = P.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_rescale_le P q)
  rw [coeff_rescale, if_neg (ne_of_gt hdeg)]
  apply mul_ne_zero _ (pow_ne_zero _ hq)
  rw [coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hdeg)

theorem rescale_one (P : Polynomial ℤ) (hP : P.coeff 0 = 0) :
    rescale P 1 = P := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [hP]
  · simp [coeff_rescale, hn]

theorem rescale_rescale (P : Polynomial ℤ) (q k : ℤ) :
    rescale (rescale P q) k = rescale P (q * k) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [coeff_rescale, hn, if_false, mul_pow]
    ring

/-- The lower coefficient bound used in the manuscript's `(C,Q)` condition.
The bound is relative to any nonzero coefficient of at least as high a degree;
in applications `e` is the original degree. -/
theorem rescale_coeff_bound (P : Polynomial ℤ) (q C : ℤ) (j e : ℕ)
    (hq : 1 ≤ q) (hC : 0 ≤ C) (hj : 0 < j) (hje : j ≤ e)
    (hcoef : |P.coeff j| ≤ C) (hlead : P.coeff e ≠ 0) :
    |(rescale P q).coeff j| ≤ C * |(rescale P q).coeff e| := by
  have he : 0 < e := lt_of_lt_of_le hj hje
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hpow : q ^ (j - 1) ≤ q ^ (e - 1) :=
    pow_le_pow_right₀ hq (Nat.sub_le_sub_right hje 1)
  have hlead1 : 1 ≤ |P.coeff e| := Int.one_le_abs hlead
  simp only [coeff_rescale, ne_of_gt hj, ne_of_gt he, if_false, abs_mul, abs_pow,
    abs_of_nonneg hq0]
  calc
    |P.coeff j| * q ^ (j - 1) ≤ C * q ^ (j - 1) :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg hq0 _)
    _ ≤ C * q ^ (e - 1) := mul_le_mul_of_nonneg_left hpow hC
    _ ≤ C * (|P.coeff e| * q ^ (e - 1)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hlead1 (pow_nonneg hq0 (e - 1))

/-- No division is needed for the fundamental rescaling identity.  The
identity remains true even for `q=0`, provided the original constant is zero. -/
theorem eval_rescale_mul (P : Polynomial ℤ) (q y : ℤ) (hP : P.coeff 0 = 0) :
    q * (rescale P q).eval y = P.eval (q * y) := by
  classical
  rw [rescale, eval_sum]
  conv_rhs => rw [eval_eq_sum]
  simp only [Polynomial.sum_def, eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : n = 0
  · subst n
    simp [hP]
  · have hpow : q * q ^ (n - 1) = q ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    simp only [hz, if_false, mul_pow]
    calc
      q * (P.coeff n * q ^ (n - 1) * y ^ n) =
          P.coeff n * (q * q ^ (n - 1)) * y ^ n := by ring
      _ = P.coeff n * (q ^ n * y ^ n) := by rw [hpow]; ring

theorem eval_rescale_ediv (P : Polynomial ℤ) (q y : ℤ)
    (hq : q ≠ 0) (hP : P.coeff 0 = 0) :
    (rescale P q).eval y = P.eval (q * y) / q := by
  rw [← eval_rescale_mul P q y hP]
  exact (Int.mul_ediv_cancel_left _ hq).symm

/-- The affine progression change used to preserve forbidden configurations
through a density increment. -/
theorem rescale_nested_eval (P : Polynomial ℤ) (q k y : ℤ)
    (hq : q ≠ 0) (hP : P.coeff 0 = 0) :
    k * (rescale P (q * k)).eval y = (rescale P q).eval (k * y) := by
  apply mul_left_cancel₀ hq
  calc
    q * (k * (rescale P (q * k)).eval y) =
        (q * k) * (rescale P (q * k)).eval y := by ring
    _ = P.eval ((q * k) * y) := eval_rescale_mul P (q * k) y hP
    _ = P.eval (q * (k * y)) := by ring_nf
    _ = q * (rescale P q).eval (k * y) :=
      (eval_rescale_mul P q (k * y) hP).symm

/-- A rescaled configuration in an affine pullback maps to a configuration
for the original integer polynomials, including preservation of distinctness.
The index type may include an index for `P₀=0`. -/
theorem configuration_affine_image {ι : Type*} (P : ι → Polynomial ℤ)
    (A : Set ℤ) (q r x y : ℤ) (hq : q ≠ 0)
    (hP : ∀ i, (P i).coeff 0 = 0)
    (hmem : ∀ i, r + q * (x + (rescale (P i) q).eval y) ∈ A)
    (hdist : Function.Injective fun i => x + (rescale (P i) q).eval y) :
    (∀ i, (r + q * x) + (P i).eval (q * y) ∈ A) ∧
      Function.Injective (fun i => (r + q * x) + (P i).eval (q * y)) := by
  have hid (i : ι) :
      (r + q * x) + (P i).eval (q * y) =
        r + q * (x + (rescale (P i) q).eval y) := by
    rw [← eval_rescale_mul (P i) q y (hP i)]
    ring
  constructor
  · intro i
    rw [hid]
    exact hmem i
  · intro i j hij
    apply hdist
    change (r + q * x) + (P i).eval (q * y) =
      (r + q * x) + (P j).eval (q * y) at hij
    rw [hid i, hid j] at hij
    exact mul_left_cancel₀ hq (add_left_cancel hij)

/-- Direct form of the configuration preservation step with successive
moduli `q` and `q*k`. The prime parameter is unchanged because
`(q*k)*y + 1 = q*(k*y) + 1`. -/
theorem configuration_rescale_affine_image {ι : Type*} (P : ι → Polynomial ℤ)
    (A : Set ℤ) (q k r x y : ℤ) (hq : q ≠ 0) (hk : k ≠ 0)
    (hP : ∀ i, (P i).coeff 0 = 0)
    (hmem : ∀ i, r + k * (x + (rescale (P i) (q * k)).eval y) ∈ A)
    (hdist : Function.Injective fun i => x + (rescale (P i) (q * k)).eval y) :
    (∀ i, (r + k * x) + (rescale (P i) q).eval (k * y) ∈ A) ∧
      Function.Injective (fun i => (r + k * x) + (rescale (P i) q).eval (k * y)) := by
  have hid (i : ι) :
      (r + k * x) + (rescale (P i) q).eval (k * y) =
        r + k * (x + (rescale (P i) (q * k)).eval y) := by
    rw [← rescale_nested_eval (P i) q k y hq (hP i)]
    ring
  constructor
  · intro i
    rw [hid]
    exact hmem i
  · intro i j hij
    apply hdist
    change (r + k * x) + (rescale (P i) q).eval (k * y) =
      (r + k * x) + (rescale (P j) q).eval (k * y) at hij
    rw [hid i, hid j] at hij
    exact mul_left_cancel₀ hk (add_left_cancel hij)

end PSPrimes
