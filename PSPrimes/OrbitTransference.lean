import PSPrimes.OrbitInputs
import PSPrimes.Homogeneity
import PSPrimes.Counting
import PSPrimes.Representatives
import PSPrimes.OrbitPolynomials
import PSPrimes.OrbitMeasureHelpers

/-!
# Finite generalized von Neumann bounds imply orbit bounds

The spatial cutoff construction is exact. This module formalizes the part of
Mousavi's orbit transference argument needed by the PS-prime theorem.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
universe u
namespace PSPrimes

/-- Restrict a complex sequence to a finite set as an actual finitely
supported function. -/
def orbitSpatialFinsupp (s : Finset ℤ) (h : ℤ → ℂ) : ℤ →₀ ℂ :=
  Finsupp.onFinset s (fun a => if a ∈ s then h a else 0)
    (by
      classical
      intro a ha
      by_contra hn
      simp [hn] at ha)

@[simp] theorem orbitSpatialFinsupp_apply (s : Finset ℤ) (h : ℤ → ℂ) (a : ℤ) :
    orbitSpatialFinsupp s h a = if a ∈ s then h a else 0 := rfl

/-- Restrict all other spatial functions to the required symmetric support. -/
def orbitSpatialCutoff (R : ℝ) (v : ℤ → ℂ) (a : ℤ) : ℂ :=
  if |(a : ℝ)| ≤ R then v a else 0

/-- The finite spatial form equals the original interval sum whenever the
shifted sampling points stay within the spatial cutoff. -/
theorem polynomialForm_orbitSpatialCutoff {ℓ : ℕ}
    (N d : ℕ) (P : Fin ℓ → Polynomial ℤ) (s : Finset ℤ)
    (h : ℤ → ℂ) (v : Fin ℓ → ℤ → ℂ) (w : ℕ → ℂ) (R : ℝ)
    (hsupport : ∀ a ∈ s, ∀ n ∈ initialInterval N, ∀ i,
      |((a + (P i).eval (n : ℤ) : ℤ) : ℝ)| ≤ R) :
    polynomialForm N d P w (orbitSpatialFinsupp s h)
      (fun i => orbitSpatialCutoff R (v i)) =
      ((N : ℂ) ^ (d + 1))⁻¹ *
        ∑ a ∈ s, ∑ n ∈ initialInterval N,
          w n * h a * ∏ i, v i (a + (P i).eval (n : ℤ)) := by
  classical
  unfold polynomialForm
  congr 1
  have hsub : (orbitSpatialFinsupp s h).support ⊆ s := by
    intro a ha
    by_contra hn
    have hz : orbitSpatialFinsupp s h a = 0 := by simp [hn]
    exact (Finsupp.mem_support_iff.mp ha) hz
  rw [Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro n hn
    simp only [orbitSpatialFinsupp_apply, if_pos ha]
    have hp : (∏ i, orbitSpatialCutoff R (v i) (a + (P i).eval (n : ℤ))) =
        ∏ i, v i (a + (P i).eval (n : ℤ)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact if_pos (hsupport a ha n hn i)
    rw [hp]
  · intro a ha hna
    have hz := Finsupp.not_mem_support_iff.mp hna
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero]

/-- Normalization of the finite spatial and time averages. -/
theorem orbitSpatial_normalization (N d : ℕ) :
    ((N : ℂ) ^ (d + 1))⁻¹ = ((N : ℂ) ^ d)⁻¹ * (N : ℂ)⁻¹ := by
  rw [pow_succ, mul_inv_rev]
  ring

/-- A bounded finite family on integer orbits inherits the fixed finite-form
estimate, with no loss in its exponent or its normalization. -/
theorem orbitSpatial_bound {ℓ : ℕ} (N d K : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (C₀ C : ℝ)
    (hfinite : ∀ (θ : ℕ → ℂ) (f₀ : ℤ →₀ ℂ)
      (f : Fin ℓ → ℤ → ℂ) (E : ℝ),
      (∀ n ∈ initialInterval N, ‖θ n‖ ≤ 1) →
      (∀ x, ‖f₀ x‖ ≤ 1) → (∀ i x, ‖f i x‖ ≤ 1) →
      (∀ x : ℤ, C₀ * (N : ℝ) ^ d < |(x : ℝ)| → f₀ x = 0) →
      (∀ i (x : ℤ), C₀ * (N : ℝ) ^ d < |(x : ℝ)| → f i x = 0) →
      0 ≤ E → PhaseBound d N θ ((N : ℝ) * E) →
      ‖polynomialForm N d P θ f₀ f‖ ≤
        C * ((N : ℝ)⁻¹ + E) ^ (1 / (K : ℝ)))
    (h : ℤ → ℂ) (v : Fin ℓ → ℤ → ℂ)
    (hh : ∀ a, ‖h a‖ ≤ 1) (hv : ∀ i a, ‖v i a‖ ≤ 1)
    (hbase : ∀ a ∈ Finset.Icc (1 : ℤ) ((N : ℤ) ^ d),
      |(a : ℝ)| ≤ C₀ * (N : ℝ) ^ d)
    (hshift : ∀ a ∈ Finset.Icc (1 : ℤ) ((N : ℤ) ^ d),
      ∀ n ∈ initialInterval N, ∀ i,
        |((a + (P i).eval (n : ℤ) : ℤ) : ℝ)| ≤ C₀ * (N : ℝ) ^ d)
    (w : ℕ → ℂ) (B E : ℝ) (hB : 0 < B) (hE : 0 ≤ E)
    (hw : ∀ n ∈ initialInterval N, ‖w n‖ ≤ B)
    (hphase : PhaseBound d N w ((N : ℝ) * E)) :
    ‖((N : ℂ) ^ d)⁻¹ *
      ∑ a ∈ Finset.Icc (1 : ℤ) ((N : ℤ) ^ d),
        h a * ((N : ℂ)⁻¹ * ∑ n ∈ initialInterval N,
          w n * ∏ i, v i (a + (P i).eval (n : ℤ)))‖ ≤
      B * C * ((N : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ)) := by
  classical
  let s := Finset.Icc (1 : ℤ) ((N : ℤ) ^ d)
  let f₀ := orbitSpatialFinsupp s h
  let f : Fin ℓ → ℤ → ℂ := fun i => orbitSpatialCutoff (C₀ * (N : ℝ) ^ d) (v i)
  have hf₀ : ∀ x, ‖f₀ x‖ ≤ 1 := by
    intro x
    dsimp [f₀]
    split_ifs
    · exact hh x
    · simp
  have hf : ∀ i x, ‖f i x‖ ≤ 1 := by
    intro i x
    dsimp [f, orbitSpatialCutoff]
    split_ifs
    · exact hv i x
    · simp
  have hf₀support : ∀ x : ℤ, C₀ * (N : ℝ) ^ d < |(x : ℝ)| → f₀ x = 0 := by
    intro x hx
    have hn : x ∉ s := fun hs => (not_lt_of_ge (hbase x hs)) hx
    simp [f₀, hn]
  have hfsupport : ∀ i (x : ℤ), C₀ * (N : ℝ) ^ d < |(x : ℝ)| → f i x = 0 := by
    intro i x hx
    exact if_neg (not_le_of_gt hx)
  have hbound := homogeneous_polynomialForm_bound N d K P f₀ f C
    (fun θ E hθ hE hp => hfinite θ f₀ f E hθ hf₀ hf hf₀support hfsupport hE hp)
    B E hB hE w hw hphase
  rw [polynomialForm_orbitSpatialCutoff N d P s h v w (C₀ * (N : ℝ) ^ d) hshift,
    orbitSpatial_normalization] at hbound
  convert hbound using 1
  simp only [s, Finset.mul_sum, mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Orbit products translated along the same integer action are the spatial
polynomial configurations used by the finite von Neumann theorem. -/
theorem orbitProduct_act {ℓ : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (P : Fin ℓ → Polynomial ℤ) (T : IntegerAction X μ)
    (f : Fin ℓ → X → ℂ) (n : ℕ) (a : ℤ) (x : X) :
    orbitProduct P T f n (T.act a x) =
      ∏ i, f i (T.act (a + (shiftedOrbitPolynomial (P i)).eval (n : ℤ)) x) := by
  unfold orbitProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_shiftedOrbitPolynomial, add_comm a, T.add_act]

/-- The finite distinct-degree generalized von Neumann estimate proves the
entire orbit interface needed by this project. The exponent is unchanged and
is selected by degree before the fixed family, while its support constant is
fixed before the probability system and the scale. In particular there is no
assumption about a result of the author's other paper. -/
theorem orbitVNInput_of_finiteVNInput (hVN : FiniteVNInput) : OrbitVNInput.{u} := by
  classical
  intro d hd
  obtain ⟨K, hK, hFamily⟩ := hVN d hd
  refine ⟨K, hK, ?_⟩
  intro ℓ P hℓ hmono hpos hmax htop
  let R : Fin ℓ → Polynomial ℤ := fun i => shiftedOrbitPolynomial (P i)
  have hRmono : StrictMono (fun i => (R i).natDegree) :=
    strictMono_shiftedOrbitPolynomial P hmono
  have hRpos : ∀ i, 1 ≤ (R i).natDegree := by simpa only [R, natDegree_shiftedOrbitPolynomial] using hpos
  have hRmax : ∀ i, (R i).natDegree ≤ d := by simpa only [R, natDegree_shiftedOrbitPolynomial] using hmax
  have hRtop : ∃ i, (R i).natDegree = d := by simpa only [R, natDegree_shiftedOrbitPolynomial] using htop
  let C₀ := orbitSupportConstant P d
  obtain ⟨C, hC, hfinite⟩ := hFamily ℓ R hℓ hRmono hRpos hRmax hRtop
    C₀ (one_le_orbitSupportConstant P d)
  refine ⟨C, hC, ?_⟩
  intro X _ μ hprob T f hf hb N hN g B E hB hE hg hp
  letI : IsProbabilityMeasure μ := hprob
  let A : X → ℂ := fun x => weightedAverage g (fun n => orbitProduct P T f n x) N
  have hA : Integrable A μ := weighted_orbitAverage_integrable P T f hf hb g N
  refine ⟨hA, ?_⟩
  let h : X → ℂ := fun x => orbitDualMultiplier (A x)
  let s : Finset ℤ := Finset.Icc 1 ((N : ℤ) ^ d)
  let V : X → ℂ := fun x => ((N : ℂ) ^ d)⁻¹ *
    ∑ a ∈ s, h (T.act a x) * A (T.act a x)
  have hPair : Integrable (fun x => h x * A x) μ := orbitDualPair_integrable hA
  have htrans (a : ℤ) : Integrable (fun x => h (T.act a x) * A (T.act a x)) μ :=
    ((T.preserving a).integrable_comp hPair.aestronglyMeasurable).2 hPair
  have hcard : (s.card : ℂ) = (N : ℂ) ^ d := by
    simp only [s, Int.card_Icc, add_sub_cancel_right, ← Nat.cast_pow, Int.toNat_natCast]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hIntegral : (∫ x, V x ∂μ) = ∫ x, h x * A x ∂μ := by
    change (∫ x, ((N : ℂ) ^ d)⁻¹ *
      ∑ a ∈ s, h (T.act a x) * A (T.act a x) ∂μ) = _
    rw [integral_const_mul, integral_finset_sum s (fun a _ => htrans a)]
    simp_rw [integerAction_integral_comp T _ (fun x => h x * A x) hPair.aestronglyMeasurable]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hNne), one_mul]
  have hpoint : ∀ᵐ x ∂μ,
      ‖V x‖ ≤ B * C * ((N : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ)) := by
    filter_upwards [ae_all_integer_iterates_bounded T f (fun _ => 1) hb] with x hx
    have hSpatial := orbitSpatial_bound N d K R C₀ C (hfinite N hN)
      (fun a => h (T.act a x)) (fun i a => f i (T.act a x))
      (fun a => norm_orbitDualMultiplier_le _) (fun i a => hx a i)
      (orbit_spatial_support_bound P d N hN)
      (by
        intro a ha n hn i
        simpa only [R, eval_shiftedOrbitPolynomial] using
          orbit_shift_support_bound P d hmax N hN a ha n hn i)
      (fun n => (g n : ℂ)) B E hB hE
      (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hg n hn) hp
    convert hSpatial using 1
    simp only [V, A, weightedAverage, orbitProduct_act, s, R]
  have hFinal := norm_integral_le_of_norm_le_const hpoint
  rw [hIntegral] at hFinal
  change ‖∫ x, orbitDualMultiplier (A x) * A x ∂μ‖ ≤ _ at hFinal
  rw [integral_orbitDualPair] at hFinal
  have hnonneg : 0 ≤ ∫ x, ‖A x‖ ∂μ := integral_nonneg (fun x => norm_nonneg _)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    measureReal_univ_eq_one, mul_one, mul_comm B C] using hFinal

end PSPrimes
