import PSPrimes.Rescaling
import PSPrimes.Counting
import PSPrimes.PhaseBounds

/-!
# Lifting changing polynomial families to a fixed family

These are the exact finite identities behind the change of variables in
Proposition 2.3. No analytic comparison estimate is assumed here.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

def multiplicationEmbedding (q : ℤ) (hq : q ≠ 0) : ℤ ↪ ℤ :=
  ⟨fun x => q * x, fun _ _ h => mul_left_cancel₀ hq h⟩

/-- Extend a function on the multiples of q by zero elsewhere. -/
def liftFunction (q : ℤ) (f : ℤ → ℂ) (z : ℤ) : ℂ :=
  if q ∣ z then f (z / q) else 0

/-- Finite support version of the same lift. -/
def liftFinsupp (q : ℤ) (hq : q ≠ 0) (f : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.embDomain (multiplicationEmbedding q hq) f

@[simp] theorem liftFinsupp_mul (q : ℤ) (hq : q ≠ 0) (f : ℤ →₀ ℂ) (x : ℤ) :
    liftFinsupp q hq f (q * x) = f x :=
  Finsupp.embDomain_apply _ _ _

@[simp] theorem liftFunction_mul (q : ℤ) (hq : q ≠ 0) (f : ℤ → ℂ) (x : ℤ) :
    liftFunction q f (q * x) = f x := by
  simp [liftFunction, Int.mul_ediv_cancel_left _ hq]

theorem liftFinsupp_eq_liftFunction (q : ℤ) (hq : q ≠ 0) (f : ℤ →₀ ℂ) (z : ℤ) :
    liftFinsupp q hq f z = liftFunction q f z := by
  classical
  by_cases hz : q ∣ z
  · obtain ⟨x, rfl⟩ := hz
    rw [liftFinsupp_mul, liftFunction_mul q hq]
  · rw [liftFunction, if_neg hz]
    apply Finsupp.embDomain_notin_range
    rintro ⟨x, hx⟩
    apply hz
    exact ⟨x, hx.symm⟩

theorem norm_liftFunction_le (q : ℤ) (f : ℤ → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) (z : ℤ) :
    ‖liftFunction q f z‖ ≤ B := by
  classical
  unfold liftFunction
  split_ifs
  · exact hf _
  · simpa using hB

theorem norm_liftFinsupp_le (q : ℤ) (hq : q ≠ 0) (f : ℤ →₀ ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) (z : ℤ) :
    ‖liftFinsupp q hq f z‖ ≤ B := by
  rw [liftFinsupp_eq_liftFunction]
  exact norm_liftFunction_le q f hB hf z

/-- The support increases by exactly the spatial dilation, with no loss from
the zero extension. The later scale comparison with `L^d` is separate. -/
theorem liftFinsupp_support_bound (q : ℤ) (hq : q ≠ 0) (f : ℤ →₀ ℂ) (R : ℤ)
    (hf : ∀ x ∈ f.support, |x| ≤ R) :
    ∀ z ∈ (liftFinsupp q hq f).support, |z| ≤ |q| * R := by
  intro z hz
  rw [liftFinsupp, Finsupp.support_embDomain] at hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
  change |q * x| ≤ |q| * R
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hf x hx) (abs_nonneg q)

/-- The support formulation used by the finite von Neumann input, for an
arbitrary real spatial radius. -/
theorem liftFunction_vanishes (q : ℤ) (f : ℤ → ℂ) (R : ℝ)
    (hf : ∀ x : ℤ, R < |(x : ℝ)| → f x = 0) :
    ∀ z : ℤ, |(q : ℝ)| * R < |(z : ℝ)| → liftFunction q f z = 0 := by
  classical
  intro z hz
  unfold liftFunction
  split_ifs with hdiv
  · obtain ⟨x, rfl⟩ := hdiv
    by_cases hq : q = 0
    · simp [hq] at hz
    · rw [Int.mul_ediv_cancel_left _ hq]
      apply hf
      have hmul : |(q : ℝ)| * R < |(q : ℝ)| * |(x : ℝ)| := by
        simpa only [Int.cast_mul, abs_mul] using hz
      by_contra hx
      have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hx) (abs_nonneg (q : ℝ))
      exact (not_lt_of_ge hle) hmul
  · rfl

theorem liftFinsupp_vanishes (q : ℤ) (hq : q ≠ 0) (f : ℤ →₀ ℂ) (R : ℝ)
    (hf : ∀ x : ℤ, R < |(x : ℝ)| → f x = 0) :
    ∀ z : ℤ, |(q : ℝ)| * R < |(z : ℝ)| → liftFinsupp q hq f z = 0 := by
  intro z hz
  rw [liftFinsupp_eq_liftFunction]
  exact liftFunction_vanishes q f R hf z hz

theorem liftFunction_rescale (P : Polynomial ℤ) (q x y : ℤ) (hq : q ≠ 0)
    (hP : P.coeff 0 = 0) (f : ℤ → ℂ) :
    liftFunction q f (q * x + P.eval (q * y)) =
      f (x + (rescale P q).eval y) := by
  rw [← eval_rescale_mul P q y hP, ← mul_add]
  exact liftFunction_mul q hq f _

def liftWeight (Q : ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  if Q ∣ n then w (n + 1) else 0

/-- Reindex precisely the positive multiples of Q in [QM]. -/
theorem sum_multiples (Q M : ℕ) (hQ : 0 < Q) (g : ℕ → ℂ) :
    (∑ n ∈ (initialInterval (Q * M)).filter (Q ∣ ·), g n) =
      ∑ y ∈ initialInterval M, g (Q * y) := by
  classical
  symm
  apply Finset.sum_bij (fun y _ => Q * y)
  · intro y hy
    simp only [initialInterval, Finset.mem_Icc] at hy
    simp only [initialInterval, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, Nat.mul_le_mul_left Q hy.2⟩, dvd_mul_right Q y⟩
    exact le_trans (Nat.succ_le_of_lt hQ) (by simpa using Nat.mul_le_mul_left Q hy.1)
  · intro y hy z hz heq
    exact Nat.eq_of_mul_eq_mul_left hQ heq
  · intro n hn
    simp only [initialInterval, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨y, rfl⟩ := hn.2
    refine ⟨y, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra hy
      have : y = 0 := by omega
      simp [this] at hn
    · exact Nat.le_of_mul_le_mul_left hn.1.2 hQ
  · intro y hy
    rfl

/-- An arbitrary summand may be multiplied by the lifted weight before the
positive-multiple reindexing; no bound or regularity is needed. -/
theorem sum_liftWeight (Q M : ℕ) (hQ : 0 < Q) (w g : ℕ → ℂ) :
    (∑ n ∈ initialInterval (Q * M), liftWeight Q w n * g n) =
      ∑ y ∈ initialInterval M, w (Q * y + 1) * g (Q * y) := by
  classical
  calc
    _ = ∑ n ∈ (initialInterval (Q * M)).filter (Q ∣ ·), w (n + 1) * g n := by
      simp [Finset.sum_filter, liftWeight]
    _ = _ := sum_multiples Q M hQ (fun n => w (n + 1) * g n)

theorem phaseSum_liftWeight (Q M : ℕ) (hQ : 0 < Q) (w : ℕ → ℂ)
    (φ : Polynomial ℝ) :
    phaseSum (Q * M) (liftWeight Q w) φ =
      phaseSum M (fun y => w (Q * y + 1))
        (φ.comp (Polynomial.C (Q : ℝ) * Polynomial.X)) := by
  unfold phaseSum
  rw [sum_liftWeight Q M hQ]
  simp [Polynomial.eval_comp, Nat.cast_mul]

/-- The polynomial-phase estimate for the progression transfers to the
multiple-supported weight at scale QM without any further factor Q. -/
theorem PhaseBound.liftWeight {r Q M : ℕ} (hQ : 0 < Q) {w : ℕ → ℂ} {E : ℝ}
    (hphase : PhaseBound r M (fun y => w (Q * y + 1)) E) :
    PhaseBound r (Q * M) (liftWeight Q w) E := by
  intro φ hφ
  rw [phaseSum_liftWeight Q M hQ]
  apply hphase
  calc
    _ ≤ φ.natDegree * (Polynomial.C (Q : ℝ) * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ φ.natDegree * 1 := Nat.mul_le_mul_left _ (by
      simpa using Polynomial.natDegree_C_mul_le (Q : ℝ) (Polynomial.X : Polynomial ℝ))
    _ ≤ r := by simpa using hφ

theorem norm_liftWeight_le (Q : ℕ) (w : ℕ → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (n : ℕ) (hw : ‖w (n + 1)‖ ≤ B) :
    ‖liftWeight Q w n‖ ≤ B := by
  classical
  unfold liftWeight
  split_ifs
  · exact hw
  · simpa using hB

/-- Exact change of both summation variables: `z=Qx`, `n=Qy`. -/
theorem lifting_sum {ℓ : ℕ} (Q M : ℕ) (hQ : 0 < Q)
    (P : Fin ℓ → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) :
    (∑ z ∈ (liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀).support,
      ∑ n ∈ initialInterval (Q * M),
        liftWeight Q w n *
          liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀ z *
          ∏ i, liftFunction (Q : ℤ) (f i) (z + (P i).eval (n : ℤ))) =
    ∑ x ∈ f₀.support, ∑ y ∈ initialInterval M,
      w (Q * y + 1) * f₀ x *
        ∏ i, f i (x + (rescale (P i) (Q : ℤ)).eval (y : ℤ)) := by
  classical
  have hq : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  rw [show (liftFinsupp (Q : ℤ) hq f₀).support =
      f₀.support.map (multiplicationEmbedding (Q : ℤ) hq) from
        Finsupp.support_embDomain _ _]
  rw [Finset.sum_map]
  change (∑ x ∈ f₀.support, ∑ n ∈ initialInterval (Q * M),
    liftWeight Q w n * liftFinsupp (Q : ℤ) hq f₀ ((Q : ℤ) * x) *
      ∏ i, liftFunction (Q : ℤ) (f i) ((Q : ℤ) * x + (P i).eval (n : ℤ))) = _
  simp only [liftFinsupp_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro x hx
  rw [sum_liftWeight Q M hQ]
  apply Finset.sum_congr rfl
  intro y hy
  simp_rw [Nat.cast_mul]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact liftFunction_rescale (P i) (Q : ℤ) x (y : ℤ) hq (hP i) (f i)

/-- The normalized lifting identity. The explicit scale factor is
`L^(d+1)/(NM)`, exactly as in the proof of Proposition 2.3. A further weight
normalization by B is handled by `polynomialForm_smul`. -/
theorem countingForm_lift {ℓ : ℕ} (N Q M d : ℕ) (hQ : 0 < Q) (hM : 0 < M)
    (P : Fin ℓ → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) :
    countingForm N M Q (fun i => rescale (P i) (Q : ℤ)) w f₀ f =
      (((Q * M : ℕ) : ℂ) ^ (d + 1) * ((N : ℂ) * (M : ℂ))⁻¹) *
        polynomialForm (Q * M) d P (liftWeight Q w)
          (liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀)
          (fun i => liftFunction (Q : ℤ) (f i)) := by
  classical
  unfold polynomialForm
  rw [lifting_sum Q M hQ P hP w f₀ f]
  unfold countingForm
  have hL : ((Q * M : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hQ hM))
  have hpow : (((Q * M : ℕ) : ℂ) ^ (d + 1)) ≠ 0 := pow_ne_zero _ hL
  calc
    _ = ((((Q * M : ℕ) : ℂ) ^ (d + 1)) *
        ((((Q * M : ℕ) : ℂ) ^ (d + 1)))⁻¹) *
        (((N : ℂ) * (M : ℂ))⁻¹ *
          ∑ x ∈ f₀.support, ∑ y ∈ initialInterval M,
            w (Q * y + 1) * f₀ x *
              ∏ i, f i (x + (rescale (P i) (Q : ℤ)).eval (y : ℤ))) := by
      rw [mul_inv_cancel₀ hpow, one_mul]
    _ = _ := by ring

end PSPrimes
