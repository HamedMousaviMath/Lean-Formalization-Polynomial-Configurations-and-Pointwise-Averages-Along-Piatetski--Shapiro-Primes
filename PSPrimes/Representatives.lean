import PSPrimes.Definitions

noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace PSPrimes

/-- An essential bound holds simultaneously along every integer iterate.
This countability argument is needed before using pointwise orbit bounds. -/
theorem ae_all_integer_iterates_bounded {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (T : IntegerAction X μ)
    (f : Fin ℓ → X → ℂ) (C : Fin ℓ → ℝ)
    (h : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C i) :
    ∀ᵐ x ∂μ, ∀ n : ℤ, ∀ i, ‖f i (T.act n x)‖ ≤ C i := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro i
  exact (T.preserving n).quasiMeasurePreserving.ae (h i)

theorem ae_all_integer_iterates_congr {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (T : IntegerAction X μ)
    (f g : Fin ℓ → X → ℂ) (h : ∀ i, f i =ᵐ[μ] g i) :
    ∀ᵐ x ∂μ, ∀ n : ℤ, ∀ i, f i (T.act n x) = g i (T.act n x) := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro i
  exact (T.preserving n).quasiMeasurePreserving.ae_eq (h i)

/-- Choose everywhere bounded versions without strengthening an L∞ hypothesis.
Strong measurability here is almost-everywhere strong measurability, as in
the main specification, and is preserved by the proved a.e. equality. -/
theorem exists_bounded_representatives {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (f : Fin ℓ → X → ℂ)
    (C : Fin ℓ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C i) :
    ∃ g : Fin ℓ → X → ℂ,
      (∀ i x, ‖g i x‖ ≤ C i) ∧
      (∀ i, f i =ᵐ[μ] g i) ∧
      (∀ i, AEStronglyMeasurable (g i) μ) := by
  classical
  let g : Fin ℓ → X → ℂ := fun i x => if ‖f i x‖ ≤ C i then f i x else 0
  have heq (i : Fin ℓ) : f i =ᵐ[μ] g i := by
    filter_upwards [hbound i] with x hx
    simp [g, hx]
  refine ⟨g, ?_, heq, ?_⟩
  · intro i x
    dsimp [g]
    split_ifs with hx
    · exact hx
    · simpa using hC i
  · intro i
    exact (hf i).congr (heq i)

theorem ae_orbitProduct_congr {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (P : Fin ℓ → Polynomial ℤ)
    (T : IntegerAction X μ) (f g : Fin ℓ → X → ℂ)
    (h : ∀ i, f i =ᵐ[μ] g i) :
    ∀ᵐ x ∂μ, ∀ n, orbitProduct P T f n x = orbitProduct P T g n x := by
  filter_upwards [ae_all_integer_iterates_congr T f g h] with x hx
  intro n
  apply Finset.prod_congr rfl
  intro i hi
  exact hx _ i

/-- The product is 1-bounded simultaneously along all sampled orbit points;
the hypotheses are essential bounds, rather than everywhere bounds. -/
theorem ae_orbitProduct_oneBounded {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (P : Fin ℓ → Polynomial ℤ)
    (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ)
    (h : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) :
    ∀ᵐ x ∂μ, ∀ n, ‖orbitProduct P T f n x‖ ≤ 1 := by
  filter_upwards [ae_all_integer_iterates_bounded T f (fun _ => 1) h] with x hx
  intro n
  unfold orbitProduct
  calc
    ‖∏ i, f i (T.act ((P i).eval ((n : ℤ) - 1)) x)‖ ≤
        ∏ i, ‖f i (T.act ((P i).eval ((n : ℤ) - 1)) x)‖ := Finset.norm_prod_le _ _
    _ ≤ 1 := Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hx _ i)

/-- The actual common-limit specification is invariant under changing the
L∞ representatives. All countably many orbit values are handled together. -/
theorem PointwiseConclusion.congr {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (P : Fin ℓ → Polynomial ℤ)
    (c : ℝ) (T : IntegerAction X μ) (f g : Fin ℓ → X → ℂ)
    (h : ∀ i, f i =ᵐ[μ] g i) :
    PointwiseConclusion P c T f ↔ PointwiseConclusion P c T g := by
  have hh := ae_orbitProduct_congr P T f g h
  have key : ∀ (a b : Fin ℓ → X → ℂ),
      (∀ᵐ x ∂μ, ∀ n, orbitProduct P T a n x = orbitProduct P T b n x) →
      PointwiseConclusion P c T a → PointwiseConclusion P c T b := by
    intro a b hab ha
    obtain ⟨L, hL⟩ := ha
    refine ⟨L, ?_⟩
    filter_upwards [hL, hab] with x hx hxeq
    have heq : (fun n => orbitProduct P T a n x) =
        (fun n => orbitProduct P T b n x) := funext hxeq
    simpa only [heq] using hx
  constructor
  · exact key f g hh
  · exact key g f (by filter_upwards [hh] with x hx; intro n; exact (hx n).symm)

theorem orbitProduct_mul_inputs {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (P : Fin ℓ → Polynomial ℤ)
    (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ) (a : Fin ℓ → ℂ)
    (n : ℕ) (x : X) :
    orbitProduct P T (fun i x => a i * f i x) n x =
      (∏ i, a i) * orbitProduct P T f n x := by
  simp [orbitProduct, Finset.prod_mul_distrib]

theorem selectedAverage_mul (S : ℕ → Prop) [DecidablePred S]
    (a : ℂ) (z : ℕ → ℂ) (N : ℕ) :
    selectedAverage S (fun n => a * z n) N = a * selectedAverage S z N := by
  simp only [selectedAverage, ← Finset.mul_sum]
  ring

theorem PointwiseConclusion.mul_inputs {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (P : Fin ℓ → Polynomial ℤ)
    (c : ℝ) (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ)
    (a : Fin ℓ → ℂ) (h : PointwiseConclusion P c T f) :
    PointwiseConclusion P c T (fun i x => a i * f i x) := by
  classical
  obtain ⟨L, hL⟩ := h
  refine ⟨fun x => (∏ i, a i) * L x, ?_⟩
  filter_upwards [hL] with x hx
  constructor
  · simpa only [orbitProduct_mul_inputs, selectedAverage_mul] using
      hx.1.const_mul (∏ i, a i)
  · simpa only [orbitProduct_mul_inputs, selectedAverage_mul] using
      hx.2.const_mul (∏ i, a i)

/-- It suffices to prove the fixed-system conclusion for essentially
1-bounded inputs. The reduction retains all measurable L∞ representatives. -/
theorem pointwiseConclusion_of_oneBounded {ℓ : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (P : Fin ℓ → Polynomial ℤ)
    (c : ℝ) (T : IntegerAction X μ)
    (hunit : ∀ g : Fin ℓ → X → ℂ,
      (∀ i, AEStronglyMeasurable (g i) μ) →
      (∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ 1) → PointwiseConclusion P c T g)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hb : ∀ i, ∃ C : ℝ, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C) :
    PointwiseConclusion P c T f := by
  classical
  choose C hC using hb
  let D : Fin ℓ → ℝ := fun i => max 1 (C i)
  have hD (i : Fin ℓ) : 0 < D i := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let g : Fin ℓ → X → ℂ := fun i x => (D i : ℂ)⁻¹ * f i x
  have hg : ∀ i, AEStronglyMeasurable (g i) μ := fun i =>
    (hf i).const_mul (D i : ℂ)⁻¹
  have hgb : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ 1 := by
    intro i
    filter_upwards [hC i] with x hx
    have hxD : ‖f i x‖ ≤ D i := hx.trans (le_max_right _ _)
    dsimp [g]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hD i)]
    calc
      (D i)⁻¹ * ‖f i x‖ ≤ (D i)⁻¹ * D i :=
        mul_le_mul_of_nonneg_left hxD (inv_nonneg.mpr (hD i).le)
      _ = 1 := inv_mul_cancel₀ (hD i).ne'
  have hh := PointwiseConclusion.mul_inputs P c T g (fun i => (D i : ℂ)) (hunit g hg hgb)
  have heq : (fun i x => (D i : ℂ) * g i x) = f := by
    funext i x
    dsimp [g]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (hD i).ne'), one_mul]
  rwa [heq] at hh

end PSPrimes
