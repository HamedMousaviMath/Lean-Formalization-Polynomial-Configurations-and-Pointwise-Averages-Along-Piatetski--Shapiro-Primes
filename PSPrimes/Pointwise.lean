import PSPrimes.Definitions

open scoped BigOperators ENNReal Topology
open Filter Finset MeasureTheory

namespace PSPrimes

attribute [local instance] Classical.propDecidable

/-- Discrete Abel summation with nonnegative forward differences for decreasing multipliers. -/
theorem sum_range_abel (f : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ range (n + 1), f i • g i) =
      f n • (∑ i ∈ range (n + 1), g i) +
        ∑ i ∈ range n, (f i - f (i + 1)) • (∑ j ∈ range (i + 1), g j) := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel, sub_smul, Finset.sum_sub_distrib]
  abel

/-- A positive Abel transform preserves domination of all partial sums. -/
theorem abel_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (v : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i ≤ n, 0 ≤ f i)
    (hdec : ∀ i < n, f (i + 1) ≤ f i)
    (hpartial : ∀ k ≤ n + 1, ‖∑ i ∈ range k, g i‖ ≤ ∑ i ∈ range k, v i) :
    ‖∑ i ∈ range (n + 1), f i • g i‖ ≤
      ∑ i ∈ range (n + 1), f i * v i := by
  rw [sum_range_abel]
  calc
    ‖f n • (∑ i ∈ range (n + 1), g i) +
        ∑ i ∈ range n, (f i - f (i + 1)) • (∑ j ∈ range (i + 1), g j)‖
      ≤ ‖f n • (∑ i ∈ range (n + 1), g i)‖ +
        ∑ i ∈ range n, ‖(f i - f (i + 1)) • (∑ j ∈ range (i + 1), g j)‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_sum_le _ _) _)
    _ ≤ f n * (∑ i ∈ range (n + 1), v i) +
        ∑ i ∈ range n, (f i - f (i + 1)) * (∑ j ∈ range (i + 1), v j) := by
      apply add_le_add
      · rw [norm_smul, Real.norm_of_nonneg (hf n le_rfl)]
        exact mul_le_mul_of_nonneg_left (hpartial (n + 1) le_rfl) (hf n le_rfl)
      · apply sum_le_sum
        intro i hi
        have hin : i < n := mem_range.mp hi
        have hp : 0 ≤ f i - f (i + 1) := sub_nonneg.mpr (hdec i hin)
        rw [norm_smul, Real.norm_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (hpartial (i + 1) (by omega)) hp
    _ = ∑ i ∈ range (n + 1), f i * v i := by
      have h := Finset.sum_range_by_parts f v (n + 1)
      simp only [Nat.add_sub_cancel, smul_eq_mul, sub_mul, Finset.sum_sub_distrib] at h ⊢
      linarith

/-- Finite unweighting estimate. A uniform additive error in weighted partial sums
costs only `C / a 0`, even if the nondecreasing positive weights are unbounded. -/
theorem finite_unweighting_bound (a : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) (C ε : ℝ)
    (ha : ∀ i, 0 < a i) (hmono : Monotone a)
    (hpartial : ∀ k ≤ n + 1,
      ‖∑ i ∈ range k, a i • z i‖ ≤ C + ε * ∑ i ∈ range k, a i) :
    ‖∑ i ∈ range (n + 1), z i‖ ≤ C / a 0 + ε * (n + 1) := by
  let v : ℕ → ℝ := fun i => ε * a i + if i = 0 then C else 0
  have hv (k : ℕ) (hk : 0 < k) :
      (∑ i ∈ range k, v i) = ε * (∑ i ∈ range k, a i) + C := by
    simp [v, Finset.sum_add_distrib, ← Finset.mul_sum, hk.ne', Nat.pos_iff_ne_zero]
  have hb := abel_norm_bound (fun i => (a i)⁻¹) (fun i => a i • z i) v n
    (fun i _ => inv_nonneg.mpr (ha i).le)
    (fun i _ => inv_le_inv₀ (ha (i + 1)) (ha i) |>.2 (hmono (Nat.le_succ i)))
    (by
      intro k hk
      by_cases hk0 : k = 0
      · simp [hk0]
      · rw [hv k (Nat.pos_of_ne_zero hk0)]
        simpa [add_comm] using hpartial k hk)
  have hl : (∑ i ∈ range (n + 1), (a i)⁻¹ • a i • z i) =
      ∑ i ∈ range (n + 1), z i := by
    apply sum_congr rfl
    intro i _
    simp [smul_smul, (ha i).ne']
  rw [hl] at hb
  have hr : (∑ i ∈ range (n + 1), (a i)⁻¹ * v i) =
      C / a 0 + ε * (n + 1) := by
    simp_rw [v, mul_add, mul_ite, mul_zero]
    rw [Finset.sum_add_distrib]
    have he : ∑ i ∈ range (n + 1), (a i)⁻¹ * (ε * a i) = ε * (n + 1) := by
      calc
        _ = ∑ i ∈ range (n + 1), ε := by
          apply sum_congr rfl
          intro i _
          field_simp [(ha i).ne']
        _ = ε * (n + 1) := by simp; ring
    rw [he]
    simp [div_eq_mul_inv]
    ring
  rwa [hr] at hb

/-- Removing a positive nondecreasing weight preserves a zero limit when
all centered weighted partial sums are little-o of the corresponding mass.
The sequence is indexed by the selected elements (for example, the selected
primes); passing from this enumeration to the cutoff parameter is separate. -/
theorem unweighting_tendsto_zero (a : ℕ → ℝ) (z : ℕ → ℂ)
    (ha : ∀ i, 0 < a i) (hmono : Monotone a)
    (hsmall : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
      ‖∑ i ∈ range k, a i • z i‖ ≤ ε * ∑ i ∈ range k, a i) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ range n, z i)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := hsmall (ε / 2) (by positivity)
  let C : ℝ := ∑ k ∈ range K, ‖∑ i ∈ range k, a i • z i‖
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => norm_nonneg _)
  have hglobal (k : ℕ) :
      ‖∑ i ∈ range k, a i • z i‖ ≤ C + ε / 2 * ∑ i ∈ range k, a i := by
    by_cases hk : k < K
    · have hle : ‖∑ i ∈ range k, a i • z i‖ ≤ C :=
        Finset.single_le_sum (fun j _ => norm_nonneg (∑ i ∈ range j, a i • z i))
          (mem_range.mpr hk)
      have hm : 0 ≤ ∑ i ∈ range k, a i :=
        sum_nonneg (fun i _ => (ha i).le)
      nlinarith
    · exact (hK k (by omega)).trans (le_add_of_nonneg_left hC)
  obtain ⟨N, hN⟩ := exists_nat_gt (C / a 0 / (ε / 2))
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn0)
  have hb := finite_unweighting_bound a z m C (ε / 2) ha hmono
    (fun k _ => hglobal k)
  have hnp : (0 : ℝ) < m + 1 := by positivity
  have hmn : (N : ℝ) < m + 1 := by exact_mod_cast hn
  have hbound : C / a 0 < ε / 2 * (m + 1) := by
    have hN' : C / a 0 / (ε / 2) < m + 1 := lt_trans hN hmn
    simpa [mul_comm] using (div_lt_iff₀ (by positivity : 0 < ε / 2)).mp hN'
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hnp.le)]
  calc
    (m + 1 : ℝ)⁻¹ * ‖∑ i ∈ range (m + 1), z i‖
      ≤ (m + 1 : ℝ)⁻¹ * (C / a 0 + ε / 2 * (m + 1)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hnp.le)
    _ < ε := by
      apply (inv_mul_lt_iff₀ hnp).mpr
      nlinarith

/-- Tonelli's argument used for the sparse sequence in Proposition 4.1.
The finite total integral of the norms is an explicit premise, not the
arithmetic comparison estimate. -/
theorem ae_tendsto_zero_of_tsum_lintegral_enorm_ne_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hs : ∑' n, ∫⁻ x, ‖f n x‖ₑ ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEMeasurable (fun x => ‖f n x‖ₑ) μ := (hf n).enorm
  rw [← lintegral_tsum hmeas] at hs
  have ha := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hs
  filter_upwards [ha] with x hx
  have hsum : Summable (fun n => (‖f n x‖₊ : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hsum.tendsto_atTop_zero

/-- Real `L¹` formulation of the Tonelli step, with integrability hypotheses
visible for every term. -/
theorem ae_tendsto_zero_of_summable_integral_norm
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℂ)
    (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable (fun n => ∫ x, ‖f n x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_tsum_lintegral_enorm_ne_top μ f (fun n => (hf n).1)
  have hi (n : ℕ) : ∫⁻ x, ‖f n x‖ₑ ∂μ = ‖∫ x, ‖f n x‖ ∂μ‖ₑ := by
    change (∫⁻ x, (‖f n x‖₊ : ℝ≥0∞) ∂μ) = _
    rw [lintegral_coe_eq_integral (fun x => ‖f n x‖₊) (hf n).norm,
      enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (f n x)))]
    simp only [coe_nnnorm]
  rw [funext hi]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)

lemma norm_weighted_sum_le (w : ℕ → ℝ) (z : ℕ → ℂ) (s : Finset ℕ)
    (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖∑ i ∈ s, w i • z i‖ ≤ ∑ i ∈ s, w i := by
  apply norm_sum_le_of_le
  intro i _
  rw [norm_smul, Real.norm_of_nonneg (hw i)]
  simpa using mul_le_mul_of_nonneg_left (hz i) (hw i)

/-- The finite interpolation estimate between a subsequence point and the
next one. Nonnegativity of the weights is essential. -/
theorem weighted_average_interpolation_bound
    (w : ℕ → ℝ) (z : ℕ → ℂ) (J N K : ℕ)
    (hJ : 0 < J) (hJN : J ≤ N) (hNK : N ≤ K)
    (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖(N : ℝ)⁻¹ • (∑ i ∈ range N, w i • z i) -
        (J : ℝ)⁻¹ • (∑ i ∈ range J, w i • z i)‖ ≤
      ((K : ℝ) - J) / (J : ℝ)^2 * (∑ i ∈ range J, w i) +
        (J : ℝ)⁻¹ * (∑ i ∈ Ico J K, w i) := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hn : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hJ hJN
  have hjn : (J : ℝ) ≤ N := by exact_mod_cast hJN
  have hnk : (N : ℝ) ≤ K := by exact_mod_cast hNK
  have hi : (N : ℝ)⁻¹ ≤ (J : ℝ)⁻¹ := (inv_le_inv₀ hn hj).2 hjn
  have hcoeff : (J : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ ((K : ℝ) - J) / (J : ℝ)^2 := by
    calc
      (J : ℝ)⁻¹ - (N : ℝ)⁻¹ = ((N : ℝ) - J) * (N : ℝ)⁻¹ * (J : ℝ)⁻¹ := by
        field_simp [hj.ne', hn.ne']
        ring_nf
        simp
      _ ≤ ((K : ℝ) - J) * (J : ℝ)⁻¹ * (J : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hj.le)
        exact mul_le_mul (by linarith) hi (inv_nonneg.mpr hn.le) (by linarith)
      _ = ((K : ℝ) - J) / (J : ℝ)^2 := by ring
  have hs := Finset.sum_range_add_sum_Ico (fun i => w i • z i) hJN
  have hid : (N : ℝ)⁻¹ • (∑ i ∈ range N, w i • z i) -
        (J : ℝ)⁻¹ • (∑ i ∈ range J, w i • z i) =
      ((N : ℝ)⁻¹ - (J : ℝ)⁻¹) • (∑ i ∈ range J, w i • z i) +
        (N : ℝ)⁻¹ • (∑ i ∈ Ico J N, w i • z i) := by
    rw [← hs, smul_add, sub_smul]
    abel
  rw [hid]
  have htail : ∑ i ∈ Ico J N, w i ≤ ∑ i ∈ Ico J K, w i := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [mem_Ico] at hi ⊢
      exact ⟨hi.1, lt_of_lt_of_le hi.2 hNK⟩
    · intro i _ _
      exact hw i
  calc
    _ ≤ ‖((N : ℝ)⁻¹ - (J : ℝ)⁻¹) • (∑ i ∈ range J, w i • z i)‖ +
        ‖(N : ℝ)⁻¹ • (∑ i ∈ Ico J N, w i • z i)‖ := norm_add_le _ _
    _ = ((J : ℝ)⁻¹ - (N : ℝ)⁻¹) * ‖∑ i ∈ range J, w i • z i‖ +
        (N : ℝ)⁻¹ * ‖∑ i ∈ Ico J N, w i • z i‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonpos (sub_nonpos.mpr hi),
        Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
      ring
    _ ≤ ((K : ℝ) - J) / (J : ℝ)^2 * (∑ i ∈ range J, w i) +
        (J : ℝ)⁻¹ * (∑ i ∈ Ico J K, w i) := by
      apply add_le_add
      · exact mul_le_mul hcoeff (norm_weighted_sum_le w z (range J) hw hz)
          (norm_nonneg _) (div_nonneg (by linarith) (sq_nonneg _))
      · exact mul_le_mul hi ((norm_weighted_sum_le w z (Ico J N) hw hz).trans htail)
          (norm_nonneg _) (inv_nonneg.mpr hj.le)
/-- Every sufficiently large integer lies in a successive-cutoff interval. -/
theorem exists_subsequence_bracket (m : ℕ → ℕ) (hm : StrictMono m) (N : ℕ)
    (hN : m 0 ≤ N) : ∃ j, m j ≤ N ∧ N < m (j + 1) := by
  have hex : ∃ j, N < m j := ⟨N + 1, (Nat.lt_succ_self N).trans_le (hm.id_le (N + 1))⟩
  have hk : Nat.find hex ≠ 0 := by
    intro hk
    have := Nat.find_spec hex
    rw [hk] at this
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
  refine ⟨j, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega))
  · simpa [hj, Nat.succ_eq_add_one] using Nat.find_spec hex

/-- Convergence along a subsequence extends to all integers if the uniform
error on each gap tends to zero. -/
theorem tendsto_of_subsequence_gap (F : ℕ → ℂ) (m : ℕ → ℕ) (hm : StrictMono m)
    (gap : ℕ → ℝ) (hgap : Tendsto gap atTop (𝓝 0)) (L : ℂ)
    (hsub : Tendsto (fun j => F (m j)) atTop (𝓝 L))
    (hbound : ∀ j N, m j ≤ N → N < m (j + 1) → dist (F N) (F (m j)) ≤ gap j) :
    Tendsto F atTop (𝓝 L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hsub (ε / 2) (by positivity)
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.mp hgap (ε / 2) (by positivity)
  refine ⟨m (max A B), ?_⟩
  intro N hN
  obtain ⟨j, hjN, hNj⟩ := exists_subsequence_bracket m hm N
    ((hm.monotone (Nat.zero_le _)).trans hN)
  have hj : max A B ≤ j := by
    by_contra h
    have hle : j + 1 ≤ max A B := by omega
    exact (not_lt_of_ge ((hm.monotone hle).trans hN)) hNj
  have hgapj : gap j < ε / 2 := by
    have := hB j ((le_max_right A B).trans hj)
    simp only [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self (gap j)) this
  calc
    dist (F N) L ≤ dist (F N) (F (m j)) + dist (F (m j)) L := dist_triangle _ _ _
    _ ≤ gap j + dist (F (m j)) L := add_le_add_right (hbound j N hjN hNj) _
    _ < ε := by have := hA j ((le_max_left A B).trans hj); linarith

/-- The total mass of a nonnegative weight on `[0,N)`. -/
def initialWeightMass (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ range N, w i

/-- The normalized weighted mean on `[0,N)`, with the Lean convention `0⁻¹ = 0`. -/
noncomputable def weightedMean (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℝ)⁻¹ • (∑ i ∈ range N, w i • z i)

/-- The uniform finite interpolation bound for successive cutoffs. -/
noncomputable def interpolationError (w : ℕ → ℝ) (m : ℕ → ℕ) (j : ℕ) : ℝ :=
  ((m (j + 1) : ℝ) - m j) / (m j : ℝ)^2 * initialWeightMass w (m j) +
    (m j : ℝ)⁻¹ * (∑ i ∈ Ico (m j) (m (j + 1)), w i)

/-- The interpolation error tends to zero solely from the asymptotic mass and
successive-cutoff ratio. This is the deterministic mass estimate in Section 4. -/
theorem interpolationError_tendsto_zero (w : ℕ → ℝ) (m : ℕ → ℕ)
    (hm : StrictMono m) (hpos : ∀ j, 0 < m j)
    (hmass : Tendsto (fun N : ℕ => initialWeightMass w N / N) atTop (𝓝 1))
    (hratio : Tendsto (fun j => (m (j + 1) : ℝ) / m j) atTop (𝓝 1)) :
    Tendsto (interpolationError w m) atTop (𝓝 0) := by
  have hmassJ := hmass.comp hm.tendsto_atTop
  have hmassK := hmassJ.comp (tendsto_add_atTop_nat 1)
  have hlim := ((hratio.sub (tendsto_const_nhds (x := (1 : ℝ)))).mul hmassJ).add
    ((hratio.mul hmassK).sub hmassJ)
  simp only [sub_self, zero_mul, one_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards with j
  have hJ : (m j : ℝ) ≠ 0 := by exact_mod_cast (hpos j).ne'
  have hK : (m (j + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (j + 1)).ne'
  have hsum : (∑ i ∈ Ico (m j) (m (j + 1)), w i) =
      initialWeightMass w (m (j + 1)) - initialWeightMass w (m j) := by
    have hs := Finset.sum_range_add_sum_Ico w (hm.monotone (Nat.le_succ j))
    dsimp [initialWeightMass]
    linarith
  dsimp [interpolationError]
  rw [hsum]
  field_simp
  ring

/-- Full-sequence comparison from sparse comparison. Both nonnegative weights
have asymptotic mass `N`; the cutoffs have successive ratio tending to one. -/
theorem weighted_comparison_of_sparse
    (w v : ℕ → ℝ) (z : ℕ → ℂ) (m : ℕ → ℕ)
    (hm : StrictMono m) (hpos : ∀ j, 0 < m j)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hmassw : Tendsto (fun N : ℕ => initialWeightMass w N / N) atTop (𝓝 1))
    (hmassv : Tendsto (fun N : ℕ => initialWeightMass v N / N) atTop (𝓝 1))
    (hratio : Tendsto (fun j => (m (j + 1) : ℝ) / m j) atTop (𝓝 1))
    (hsparse : Tendsto (fun j => weightedMean w z (m j) - weightedMean v z (m j))
      atTop (𝓝 0)) :
    Tendsto (fun N => weightedMean w z N - weightedMean v z N) atTop (𝓝 0) := by
  have hgap := (interpolationError_tendsto_zero w m hm hpos hmassw hratio).add
    (interpolationError_tendsto_zero v m hm hpos hmassv hratio)
  simp only [add_zero] at hgap
  apply tendsto_of_subsequence_gap _ m hm _ hgap 0 hsparse
  intro j N hjN hNj
  have hbw := weighted_average_interpolation_bound w z (m j) N (m (j + 1))
    (hpos j) hjN hNj.le hw hz
  have hbv := weighted_average_interpolation_bound v z (m j) N (m (j + 1))
    (hpos j) hjN hNj.le hv hz
  change ‖(weightedMean w z N - weightedMean v z N) -
      (weightedMean w z (m j) - weightedMean v z (m j))‖ ≤ _
  have hid : (weightedMean w z N - weightedMean v z N) -
      (weightedMean w z (m j) - weightedMean v z (m j)) =
      (weightedMean w z N - weightedMean w z (m j)) -
        (weightedMean v z N - weightedMean v z (m j)) := by abel
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add hbw hbv)

/-- Almost-everywhere version of the full-sequence comparison step.
No arithmetic estimate is assumed here: sparse comparison is the input
which the separate `L¹` estimate and Tonelli lemma must supply. -/
theorem ae_weighted_comparison_of_sparse
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w v : ℕ → ℝ) (z : ℕ → X → ℂ) (m : ℕ → ℕ)
    (hm : StrictMono m) (hpos : ∀ j, 0 < m j)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hz : ∀ i, ∀ᵐ x ∂μ, ‖z i x‖ ≤ 1)
    (hmassw : Tendsto (fun N : ℕ => initialWeightMass w N / N) atTop (𝓝 1))
    (hmassv : Tendsto (fun N : ℕ => initialWeightMass v N / N) atTop (𝓝 1))
    (hratio : Tendsto (fun j => (m (j + 1) : ℝ) / m j) atTop (𝓝 1))
    (hsparse : ∀ᵐ x ∂μ, Tendsto
      (fun j => weightedMean w (fun i => z i x) (m j) -
        weightedMean v (fun i => z i x) (m j)) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto
      (fun N => weightedMean w (fun i => z i x) N -
        weightedMean v (fun i => z i x) N) atTop (𝓝 0) := by
  filter_upwards [eventually_countable_forall.2 hz, hsparse] with x hzx hx
  exact weighted_comparison_of_sparse w v (fun i => z i x) m hm hpos hw hv hzx
    hmassw hmassv hratio hx

/-- The increasing prime weight removed by partial summation in Theorem 1.2. -/
noncomputable def primeRemovalWeight (γ t : ℝ) : ℝ := γ⁻¹ * t ^ (1 - γ) * Real.log t

theorem primeRemovalWeight_pos {γ t : ℝ} (hγ : 0 < γ) (ht : 2 ≤ t) :
    0 < primeRemovalWeight γ t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 < t := by linarith
  exact mul_pos (mul_pos (inv_pos.mpr hγ) (Real.rpow_pos_of_pos ht0 _))
    (Real.log_pos ht1)

theorem primeRemovalWeight_monotoneOn {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    MonotoneOn (primeRemovalWeight γ) (Set.Ici 2) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by simp only [Set.mem_Ici] at hx; linarith
  have hx1 : 1 ≤ x := by simp only [Set.mem_Ici] at hx; linarith
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le hxy (sub_nonneg.mpr hγ1))
      (inv_nonneg.mpr hγ.le))
    (Real.log_le_log hx0 hxy) (Real.log_nonneg hx1)
    (mul_nonneg (inv_nonneg.mpr hγ.le) (Real.rpow_nonneg (hx0.le.trans hxy) _))

@[simp] theorem primeRemovalWeight_one (t : ℝ) : primeRemovalWeight 1 t = Real.log t := by
  simp [primeRemovalWeight]

/-- For an increasing positive enumeration of a selected set, the cutoff
cardinality counts precisely the initial segment of that enumeration. -/
theorem enumeration_le_iff_lt_count (S : ℕ → Prop) [DecidablePred S]
    (e : ℕ → ℕ) (he : StrictMono e) (hpos : ∀ i, 1 ≤ e i)
    (henum : ∀ p, S p ↔ ∃ i, e i = p) (i N : ℕ) :
    e i ≤ N ↔ i < ((initialInterval N).filter S).card := by
  let s := (initialInterval N).filter S
  constructor
  · intro hi
    have hsub : (range (i + 1)).image e ⊆ s := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
      have hji : j ≤ i := by have := mem_range.mp hj; omega
      simp only [s, mem_filter, initialInterval, mem_Icc]
      exact ⟨⟨hpos j, (he.monotone hji).trans hi⟩, (henum (e j)).2 ⟨j, rfl⟩⟩
    have hc := card_le_card hsub
    rw [card_image_of_injective _ he.injective, card_range] at hc
    dsimp [s] at hc
    omega
  · intro hi
    by_contra hn
    have hsub : s ⊆ (range i).image e := by
      intro p hp
      have hp' := mem_filter.mp hp
      obtain ⟨j, rfl⟩ := (henum p).1 hp'.2
      have hjN : e j ≤ N := (mem_Icc.mp hp'.1).2
      have hji : j < i :=
        lt_of_not_ge (fun hij => hn ((he.monotone hij).trans hjN))
      exact mem_image.mpr ⟨j, mem_range.mpr hji, rfl⟩
    have hc := card_le_card hsub
    rw [card_image_of_injective _ he.injective, card_range] at hc
    dsimp [s] at hc
    omega

/-- Exact finite reindexing of selected cutoff sums; this proves the bridge,
rather than assuming equality of the two averages. -/
theorem selected_sum_eq_enumeration (S : ℕ → Prop) [DecidablePred S]
    (e : ℕ → ℕ) (he : StrictMono e) (hpos : ∀ i, 1 ≤ e i)
    (henum : ∀ p, S p ↔ ∃ i, e i = p) {E : Type*} [AddCommMonoid E]
    (z : ℕ → E) (N : ℕ) :
    (∑ p ∈ (initialInterval N).filter S, z p) =
      ∑ i ∈ range (((initialInterval N).filter S).card), z (e i) := by
  have hs : (initialInterval N).filter S =
      (range (((initialInterval N).filter S).card)).image e := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, rfl⟩ := (henum p).1 (mem_filter.mp hp).2
      exact mem_image.mpr ⟨i, mem_range.mpr
        ((enumeration_le_iff_lt_count S e he hpos henum i N).1
          (mem_Icc.mp (mem_filter.mp hp).1).2), rfl⟩
    · intro hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      simp only [mem_filter, initialInterval, mem_Icc]
      exact ⟨⟨hpos i, (enumeration_le_iff_lt_count S e he hpos henum i N).2
        (mem_range.mp hi)⟩, (henum (e i)).2 ⟨i, rfl⟩⟩
  conv_lhs => rw [hs]
  rw [Finset.sum_image]
  intro i _ j _ hij
  exact he.injective hij

/-- An increasing enumeration forces the number of selected cutoff elements
to tend to infinity. -/
theorem selected_count_tendsto_atTop (S : ℕ → Prop) [DecidablePred S]
    (e : ℕ → ℕ) (he : StrictMono e) (hpos : ∀ i, 1 ≤ e i)
    (henum : ∀ p, S p ↔ ∃ i, e i = p) :
    Tendsto (fun N => ((initialInterval N).filter S).card) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro k
  refine ⟨e k, ?_⟩
  intro N hN
  exact (enumeration_le_iff_lt_count S e he hpos henum k N).1 hN |>.le

/-- The selected average equals the ordinary average along the initial segment
of any increasing positive enumeration of the selected set. -/
theorem selectedAverage_eq_enumeration (S : ℕ → Prop) [DecidablePred S]
    (e : ℕ → ℕ) (he : StrictMono e) (hpos : ∀ i, 1 ≤ e i)
    (henum : ∀ p, S p ↔ ∃ i, e i = p) (z : ℕ → ℂ) (N : ℕ) :
    selectedAverage S z N =
      ((((initialInterval N).filter S).card : ℝ)⁻¹) •
        ∑ i ∈ range (((initialInterval N).filter S).card), z (e i) := by
  dsimp only [selectedAverage]
  rw [selected_sum_eq_enumeration S e he hpos henum]
  simp [Complex.real_smul, Complex.ofReal_inv]

/-- Unweighting for the actual selected cutoff average, with the enumeration
bridge and divergence of the selected count proved above. -/
theorem selectedAverage_unweighting_zero
    (S : ℕ → Prop) [DecidablePred S] (e : ℕ → ℕ)
    (he : StrictMono e) (hpos : ∀ i, 1 ≤ e i)
    (henum : ∀ p, S p ↔ ∃ i, e i = p)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (hmono : Monotone a) (z : ℕ → ℂ)
    (hsmall : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
      ‖∑ i ∈ range k, a i • z (e i)‖ ≤ ε * ∑ i ∈ range k, a i) :
    Tendsto (selectedAverage S z) atTop (𝓝 0) := by
  have hlim := (unweighting_tendsto_zero a (fun i => z (e i)) ha hmono hsmall).comp
    (selected_count_tendsto_atTop S e he hpos henum)
  apply hlim.congr'
  filter_upwards with N
  exact (selectedAverage_eq_enumeration S e he hpos henum z N).symm

/-- Centering commutes with the selected average once the cutoff set is
nonempty. The nonempty hypothesis is necessary under the zero-denominator
convention. -/
theorem selectedAverage_sub_const (S : ℕ → Prop) [DecidablePred S]
    (z : ℕ → ℂ) (L : ℂ) (N : ℕ) (hc : ((initialInterval N).filter S).card ≠ 0) :
    selectedAverage S (fun n => z n - L) N = selectedAverage S z N - L := by
  dsimp only [selectedAverage]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_sub]
  have hcz : ((((initialInterval N).filter S).card : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc
  simp [hcz]

/-- General selected-cutoff unweighting theorem with its common limit explicit.
The remaining arithmetic work in Theorem 1.2 supplies `hsmall` after the
higher-prime-power removal and the weighted mass asymptotic. -/
theorem selectedAverage_unweighting
    (S : ℕ → Prop) [DecidablePred S] (e : ℕ → ℕ)
    (he : StrictMono e) (hpos : ∀ i, 1 ≤ e i)
    (henum : ∀ p, S p ↔ ∃ i, e i = p)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (hmono : Monotone a) (z : ℕ → ℂ) (L : ℂ)
    (hsmall : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
      ‖∑ i ∈ range k, a i • (z (e i) - L)‖ ≤ ε * ∑ i ∈ range k, a i) :
    Tendsto (selectedAverage S z) atTop (𝓝 L) := by
  have hz := selectedAverage_unweighting_zero S e he hpos henum a ha hmono
    (fun n => z n - L) hsmall
  have hlim := hz.add_const L
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [(selected_count_tendsto_atTop S e he hpos henum).eventually
    (eventually_ge_atTop 1)] with N hN
  rw [selectedAverage_sub_const S z L N (by omega)]
  exact sub_add_cancel _ _

/-- Exact conversion between the manuscript's `[1,N]` convention and the
zero-based initial sums used by the generic analytic lemmas. -/
theorem sum_initialInterval_eq_range_shift {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (N : ℕ) :
    (∑ n ∈ initialInterval N, f n) = ∑ i ∈ range N, f (i + 1) := by
  simpa only [initialInterval, range_eq_Ico, zero_add, Nat.Ico_succ_right] using
    (Finset.sum_Ico_add' f 0 N 1).symm

theorem weightedAverage_eq_weightedMean_shift
    (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) :
    weightedAverage w z N = weightedMean (fun i => w (i + 1)) (fun i => z (i + 1)) N := by
  simp [weightedAverage, weightedMean, sum_initialInterval_eq_range_shift,
    Complex.real_smul, Complex.ofReal_inv]

/-- Integer power cutoffs suffice for the subsequence argument; choosing an
integer exponent larger than `η⁻¹` is allowed in the manuscript. -/
def polynomialCutoff (k j : ℕ) : ℕ := (j + 1) ^ k

theorem polynomialCutoff_strictMono {k : ℕ} (hk : k ≠ 0) :
    StrictMono (polynomialCutoff k) := by
  intro i j hij
  exact Nat.pow_lt_pow_left (Nat.add_lt_add_right hij 1) hk

theorem polynomialCutoff_pos (k j : ℕ) : 0 < polynomialCutoff k j :=
  pow_pos (Nat.zero_lt_succ j) _

theorem polynomialCutoff_ratio (k : ℕ) :
    Tendsto (fun j => (polynomialCutoff k (j + 1) : ℝ) / polynomialCutoff k j)
      atTop (𝓝 1) := by
  have hbase := (tendsto_const_nhds (x := (1 : ℝ))).add
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hp := hbase.pow k
  simp only [add_zero, one_pow] at hp
  apply hp.congr'
  filter_upwards with j
  simp only [polynomialCutoff, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [← div_pow]
  congr 1
  field_simp

theorem polynomialCutoff_summable_decay (k : ℕ) (η : ℝ) (hkη : 1 < (k : ℝ) * η) :
    Summable (fun j => (polynomialCutoff k j : ℝ) ^ (-η)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ ((k : ℝ) * (-η))) :=
    Real.summable_nat_rpow.mpr (by nlinarith)
  have hss := (summable_nat_add_iff 1).2 hs
  convert hss using 1
  ext j
  simp only [polynomialCutoff, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  exact (Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ j + 1) k (-η)).symm

noncomputable def selectedWeightMass (S : ℕ → Prop) [DecidablePred S]
    (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ (initialInterval N).filter S, w n

noncomputable def selectedWeightedSum (S : ℕ → Prop) [DecidablePred S]
    (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ (initialInterval N).filter S, (w n : ℂ) * z n

/-- Linear asymptotic selected mass already implies that the selected set
is infinite; no separate prime-counting asymptotic is used for this step. -/
theorem selected_infinite_of_mass_limit (S : ℕ → Prop) [DecidablePred S]
    (hpositive : ∀ n, S n → 1 ≤ n) (w : ℕ → ℝ)
    (hmass : Tendsto (fun N : ℕ => selectedWeightMass S w N / N) atTop (𝓝 1)) :
    (setOf S).Infinite := by
  classical
  by_contra h
  have hf : (setOf S).Finite := Set.not_infinite.mp h
  let B : ℕ := hf.toFinset.sup id
  let C : ℝ := ∑ n ∈ hf.toFinset, w n
  have heq (N : ℕ) (hN : B ≤ N) : selectedWeightMass S w N = C := by
    have hs : (initialInterval N).filter S = hf.toFinset := by
      ext n
      constructor
      · intro hn
        exact hf.mem_toFinset.mpr (mem_filter.mp hn).2
      · intro hn
        have hSn : S n := hf.mem_toFinset.mp hn
        have hnB : n ≤ B := Finset.le_sup (f := id) hn
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpositive n hSn, hnB.trans hN⟩, hSn⟩
    simp [selectedWeightMass, hs, C]
  have hz := tendsto_const_div_atTop_nhds_zero_nat C
  have hm0 : Tendsto (fun N : ℕ => selectedWeightMass S w N / N) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_ge_atTop B] with N hN
    rw [heq N hN]
  have := tendsto_nhds_unique hmass hm0
  norm_num at this

/-- The cutoff at the `i`th selected element contains exactly `i+1` elements. -/
theorem selected_count_at_enumeration (S : ℕ → Prop) [DecidablePred S]
    (e : ℕ → ℕ) (he : StrictMono e) (hpos : ∀ i, 1 ≤ e i)
    (henum : ∀ p, S p ↔ ∃ i, e i = p) (i : ℕ) :
    ((initialInterval (e i)).filter S).card = i + 1 := by
  have hlo := (enumeration_le_iff_lt_count S e he hpos henum i (e i)).1 le_rfl
  have hhi : ¬ i + 1 < ((initialInterval (e i)).filter S).card := by
    intro h
    have heq := (enumeration_le_iff_lt_count S e he hpos henum (i + 1) (e i)).2 h
    have hlt : e i < e (i + 1) := he (by omega)
    omega
  omega

/-- The complex ratio of the centered weighted sum to its selected mass tends
to zero whenever both normalized cutoff limits are known. -/
theorem selected_centered_ratio_tendsto (S : ℕ → Prop) [DecidablePred S]
    (w : ℕ → ℝ) (z : ℕ → ℂ) (L : ℂ)
    (hmass : Tendsto (fun N : ℕ => selectedWeightMass S w N / N) atTop (𝓝 1))
    (hsum : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * selectedWeightedSum S w z N)
      atTop (𝓝 L)) :
    Tendsto (fun N => selectedWeightedSum S w (fun n => z n - L) N /
      (selectedWeightMass S w N : ℂ)) atTop (𝓝 0) := by
  have hmassC := Complex.continuous_ofReal.continuousAt.tendsto.comp hmass
  simp only [Complex.ofReal_one] at hmassC
  have hc := hsum.sub (hmassC.mul_const L)
  simp only [one_mul, sub_self] at hc
  have hdiv := hc.div hmassC (by norm_num : (1 : ℂ) ≠ 0)
  simp only [zero_div] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  dsimp [selectedWeightedSum, selectedWeightMass]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

/-- End-to-end weight removal for selected integer cutoffs. Infinitude, the
increasing enumeration, the exact reindexing, and the little-o bridge are
proved internally. The two normalized limits are the precise hypotheses
established before partial summation in the manuscript. -/
theorem selectedAverage_tendsto_of_weighted_limits
    (S : ℕ → Prop) [DecidablePred S] (hpositive : ∀ n, S n → 1 ≤ n)
    (w : ℕ → ℝ) (z : ℕ → ℂ) (L : ℂ)
    (hwpos : ∀ n, S n → 0 < w n)
    (hwmono : ∀ p q, S p → S q → p ≤ q → w p ≤ w q)
    (hmass : Tendsto (fun N : ℕ => selectedWeightMass S w N / N) atTop (𝓝 1))
    (hsum : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * selectedWeightedSum S w z N)
      atTop (𝓝 L)) :
    Tendsto (selectedAverage S z) atTop (𝓝 L) := by
  classical
  have hInf := selected_infinite_of_mass_limit S hpositive w hmass
  let e := Nat.nth S
  have he : StrictMono e := Nat.nth_strictMono hInf
  have hSe (i : ℕ) : S (e i) := Nat.nth_mem_of_infinite hInf i
  have hpos (i : ℕ) : 1 ≤ e i := hpositive _ (hSe i)
  have henum (p : ℕ) : S p ↔ ∃ i, e i = p := by
    constructor
    · intro hp
      have hp' : p ∈ Set.range (Nat.nth S) := by
        rw [Nat.range_nth_of_infinite hInf]
        exact hp
      exact hp'
    · rintro ⟨i, rfl⟩
      exact hSe i
  have haw (i : ℕ) : 0 < w (e i) := hwpos _ (hSe i)
  have ham : Monotone (fun i => w (e i)) := by
    intro i j hij
    exact hwmono _ _ (hSe i) (hSe j) (he.monotone hij)
  apply selectedAverage_unweighting S e he hpos henum _ haw ham z L
  have hrat := ((selected_centered_ratio_tendsto S w z L hmass hsum).norm).comp
    he.tendsto_atTop
  simp only [norm_zero] at hrat
  intro ε hε
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hrat ε hε
  refine ⟨J + 1, ?_⟩
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hcount := selected_count_at_enumeration S e he hpos henum j
  have hmassEq : selectedWeightMass S w (e j) =
      ∑ i ∈ range (j + 1), w (e i) := by
    unfold selectedWeightMass
    rw [selected_sum_eq_enumeration S e he hpos henum w, hcount]
  have hmpos : 0 < selectedWeightMass S w (e j) := by
    rw [hmassEq]
    apply sum_pos'
    · intro i _
      exact (haw i).le
    · exact ⟨0, mem_range.mpr (by omega), haw 0⟩
  have hratj : ‖selectedWeightedSum S w (fun n => z n - L) (e j) /
      (selectedWeightMass S w (e j) : ℂ)‖ < ε := by
    simpa only [Function.comp_apply, dist_zero_right, norm_norm] using hJ j (by omega)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hmpos.le] at hratj
  have hb := (div_lt_iff₀ hmpos).mp hratj
  have hsumEq : selectedWeightedSum S w (fun n => z n - L) (e j) =
      ∑ i ∈ range (j + 1), w (e i) • (z (e i) - L) := by
    unfold selectedWeightedSum
    rw [selected_sum_eq_enumeration S e he hpos henum, hcount]
    simp only [Complex.real_smul]
  simp only [Nat.succ_eq_add_one]
  rw [← hsumEq, ← hmassEq]
  exact hb.le

/-- A power saving in the `L¹` comparison is sufficient for the full a.e.
comparison. The integer power subsequence, summability, Tonelli step,
and interpolation are all proved in this module. The arithmetic `L¹` rate
remains the separate substantive input to this generic analytic theorem. -/
theorem ae_weighted_comparison_of_L1_decay
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w v : ℕ → ℝ) (z : ℕ → X → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hz : ∀ i, ∀ᵐ x ∂μ, ‖z i x‖ ≤ 1)
    (hmassw : Tendsto (fun N : ℕ => initialWeightMass w N / N) atTop (𝓝 1))
    (hmassv : Tendsto (fun N : ℕ => initialWeightMass v N / N) atTop (𝓝 1))
    (η C : ℝ) (hη : 0 < η)
    (hint : ∀ N, Integrable
      (fun x => weightedMean w (fun i => z i x) N - weightedMean v (fun i => z i x) N) μ)
    (hL1 : ∀ N, 1 ≤ N →
      (∫ x, ‖weightedMean w (fun i => z i x) N -
        weightedMean v (fun i => z i x) N‖ ∂μ) ≤ C * (N : ℝ)^(-η)) :
    ∀ᵐ x ∂μ, Tendsto
      (fun N => weightedMean w (fun i => z i x) N -
        weightedMean v (fun i => z i x) N) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (1 / η))
  have hkη : 1 < (k : ℝ) * η :=
    (div_lt_iff₀ hη).mp ((le_max_right 1 (1 / η)).trans_lt hk)
  have hkn : k ≠ 0 := by
    have hkpos : (0 : ℝ) < k := lt_trans zero_lt_one ((le_max_left 1 (1 / η)).trans_lt hk)
    exact_mod_cast hkpos.ne'
  let m := polynomialCutoff k
  have hm : StrictMono m := polynomialCutoff_strictMono hkn
  have hpos (j : ℕ) : 0 < m j := polynomialCutoff_pos k j
  have hs : Summable (fun j => ∫ x,
      ‖weightedMean w (fun i => z i x) (m j) -
        weightedMean v (fun i => z i x) (m j)‖ ∂μ) := by
    apply ((polynomialCutoff_summable_decay k η hkη).mul_left C).of_nonneg_of_le
    · intro j
      exact integral_nonneg (fun x => norm_nonneg _)
    · intro j
      exact hL1 (m j) (hpos j)
  have hsparse := ae_tendsto_zero_of_summable_integral_norm μ
    (fun j x => weightedMean w (fun i => z i x) (m j) -
      weightedMean v (fun i => z i x) (m j)) (fun j => hint (m j)) hs
  exact ae_weighted_comparison_of_sparse μ w v z m hm hpos hw hv hz hmassw hmassv
    (polynomialCutoff_ratio k) hsparse

/-- The same analytic implication in the manuscript's exact `[1,N]`
normalization. This is the final reduction needed in Proposition 4.1 once
the separate arithmetic `L¹` estimate and the two mass asymptotics are known. -/
theorem ae_weightedAverage_comparison_of_L1_decay
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w v : ℕ → ℝ) (z : ℕ → X → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hz : ∀ i, ∀ᵐ x ∂μ, ‖z i x‖ ≤ 1)
    (hmassw : Tendsto (fun N : ℕ => (∑ i ∈ initialInterval N, w i) / N) atTop (𝓝 1))
    (hmassv : Tendsto (fun N : ℕ => (∑ i ∈ initialInterval N, v i) / N) atTop (𝓝 1))
    (η C : ℝ) (hη : 0 < η)
    (hint : ∀ N, Integrable
      (fun x => weightedAverage w (fun i => z i x) N - weightedAverage v (fun i => z i x) N) μ)
    (hL1 : ∀ N, 1 ≤ N →
      (∫ x, ‖weightedAverage w (fun i => z i x) N -
        weightedAverage v (fun i => z i x) N‖ ∂μ) ≤ C * (N : ℝ)^(-η)) :
    ∀ᵐ x ∂μ, Tendsto
      (fun N => weightedAverage w (fun i => z i x) N -
        weightedAverage v (fun i => z i x) N) atTop (𝓝 0) := by
  have hmw : Tendsto (fun N : ℕ => initialWeightMass (fun i => w (i + 1)) N / N)
      atTop (𝓝 1) := by
    simpa only [initialWeightMass, sum_initialInterval_eq_range_shift] using hmassw
  have hmv : Tendsto (fun N : ℕ => initialWeightMass (fun i => v (i + 1)) N / N)
      atTop (𝓝 1) := by
    simpa only [initialWeightMass, sum_initialInterval_eq_range_shift] using hmassv
  have hr := ae_weighted_comparison_of_L1_decay μ (fun i => w (i + 1))
    (fun i => v (i + 1)) (fun i x => z (i + 1) x)
    (fun i => hw (i + 1)) (fun i => hv (i + 1)) (fun i => hz (i + 1)) hmw hmv η C hη
    (by simpa only [weightedAverage_eq_weightedMean_shift] using hint)
    (by simpa only [weightedAverage_eq_weightedMean_shift] using hL1)
  simpa only [weightedAverage_eq_weightedMean_shift] using hr

/-- Weight removal specialized to any subset of primes, including ordinary
and Piatetski--Shapiro primes, with the paper's arithmetic weight. -/
theorem selected_primes_unweighting
    (S : ℕ → Prop) [DecidablePred S] (hprime : ∀ p, S p → p.Prime)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (z : ℕ → ℂ) (L : ℂ)
    (hmass : Tendsto (fun N : ℕ =>
      selectedWeightMass S (fun p => primeRemovalWeight γ p) N / N) atTop (𝓝 1))
    (hsum : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      selectedWeightedSum S (fun p => primeRemovalWeight γ p) z N) atTop (𝓝 L)) :
    Tendsto (selectedAverage S z) atTop (𝓝 L) := by
  apply selectedAverage_tendsto_of_weighted_limits S
    (fun p hp => (hprime p hp).one_lt.le) _ z L _ _ hmass hsum
  · intro p hp
    apply primeRemovalWeight_pos hγ
    exact_mod_cast (hprime p hp).two_le
  · intro p q hp hq hpq
    apply primeRemovalWeight_monotoneOn hγ hγ1
    · change (2 : ℝ) ≤ p
      exact_mod_cast (hprime p hp).two_le
    · change (2 : ℝ) ≤ q
      exact_mod_cast (hprime q hq).two_le
    · exact_mod_cast hpq

/-- The residual from nonprime indices in a Mangoldt-weighted average. -/
noncomputable def nonprimeWeightedMean (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ (initialInterval N).filter (fun n => ¬n.Prime), (w n : ℂ) * z n

/-- The nonprime residual has the stated positive-mass majorant. -/
theorem nonprimeWeightedMean_norm_le (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ)
    (hw : ∀ n, 0 ≤ w n) (hz : ∀ n, ‖z n‖ ≤ 1) :
    ‖nonprimeWeightedMean w z N‖ ≤ (N : ℝ)⁻¹ *
      ∑ n ∈ (initialInterval N).filter (fun n => ¬n.Prime), w n := by
  unfold nonprimeWeightedMean
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [Complex.real_smul] using
    norm_weighted_sum_le w z ((initialInterval N).filter (fun n => ¬n.Prime)) hw hz

/-- On prime indices the sparse Mangoldt function gives exactly the selected
Piatetski--Shapiro prime sum with weight `aγ`. -/
theorem sparse_prime_sum_eq_selected (γ : ℝ) (z : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ (initialInterval N).filter Nat.Prime, (sparseMangoldt γ n : ℂ) * z n) =
      selectedWeightedSum (IsPSPrime (1 / γ)) (fun n => primeRemovalWeight γ n) z N := by
  classical
  unfold selectedWeightedSum
  simp only [Finset.sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · rw [if_pos hp, sparseMangoldt_prime γ hp]
    by_cases hs : IsPSPrime (1 / γ) n
    · simp only [if_pos hs, primeRemovalWeight]
    · simp only [if_neg hs, Complex.ofReal_zero, zero_mul]
  · simp [hp, IsPSPrime]

/-- Exact sparse prime / higher-prime-power decomposition, before any estimate. -/
theorem sparse_weightedAverage_decomposition (γ : ℝ) (z : ℕ → ℂ) (N : ℕ) :
    weightedAverage (sparseMangoldt γ) z N =
      (N : ℂ)⁻¹ * selectedWeightedSum (IsPSPrime (1 / γ))
        (fun n => primeRemovalWeight γ n) z N +
      nonprimeWeightedMean (sparseMangoldt γ) z N := by
  classical
  dsimp [weightedAverage, nonprimeWeightedMean]
  rw [← sparse_prime_sum_eq_selected γ z N, ← mul_add,
    Finset.sum_filter_add_sum_filter_not]

/-- Exact ordinary prime / higher-prime-power decomposition. -/
theorem ordinary_weightedAverage_decomposition (z : ℕ → ℂ) (N : ℕ) :
    weightedAverage ArithmeticFunction.vonMangoldt z N =
      (N : ℂ)⁻¹ * selectedWeightedSum Nat.Prime (fun n => Real.log n) z N +
      nonprimeWeightedMean ArithmeticFunction.vonMangoldt z N := by
  classical
  have hs : (∑ n ∈ (initialInterval N).filter Nat.Prime,
      (ArithmeticFunction.vonMangoldt n : ℂ) * z n) =
      selectedWeightedSum Nat.Prime (fun n => Real.log n) z N := by
    apply sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hn).2]
  dsimp [weightedAverage, nonprimeWeightedMean]
  rw [← hs, ← mul_add, Finset.sum_filter_add_sum_filter_not]

/-- Nonprime indices where a Mangoldt weight can survive are genuine higher
prime powers. The exponent is at least two, as required in the manuscript. -/
theorem exists_higher_prime_power {n : ℕ} (hn : ¬n.Prime) (hpow : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p^k = n := by
  obtain ⟨p, k, hp, hk, hpk⟩ := hpow
  have hpn : p.Prime := Nat.prime_iff.mpr hp
  have hk1 : k ≠ 1 := by
    intro hk1
    subst k
    simp only [pow_one] at hpk
    exact hn (hpk ▸ hpn)
  exact ⟨p, k, hpn, by omega, hpk⟩

theorem sparseMangoldt_eq_zero_of_not_isPrimePow (γ : ℝ) {n : ℕ} (hn : ¬IsPrimePow n) :
    sparseMangoldt γ n = 0 := by
  have hv := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  simp [sparseMangoldt, hv]

/-- A Mangoldt-supported nonprime residual can be written entirely over
higher prime powers; this is an exact support statement, not its quantitative
estimate. -/
theorem nonprimeWeightedMean_eq_primePower_sum
    (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ)
    (hzero : ∀ n, ¬IsPrimePow n → w n = 0) :
    nonprimeWeightedMean w z N = (N : ℂ)⁻¹ *
      ∑ n ∈ (initialInterval N).filter (fun n => ¬n.Prime ∧ IsPrimePow n),
        (w n : ℂ) * z n := by
  unfold nonprimeWeightedMean
  congr 1
  simp only [Finset.sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp [hp]
  · by_cases hpp : IsPrimePow n
    · simp [hp, hpp]
    · simp [hp, hpp, hzero n hpp]

theorem sparse_nonprimeWeightedMean_eq_primePower_sum (γ : ℝ) (z : ℕ → ℂ) (N : ℕ) :
    nonprimeWeightedMean (sparseMangoldt γ) z N = (N : ℂ)⁻¹ *
      ∑ n ∈ (initialInterval N).filter (fun n => ¬n.Prime ∧ IsPrimePow n),
        (sparseMangoldt γ n : ℂ) * z n :=
  nonprimeWeightedMean_eq_primePower_sum _ z N
    (fun _ hn => sparseMangoldt_eq_zero_of_not_isPrimePow γ hn)

theorem ordinary_nonprimeWeightedMean_eq_primePower_sum (z : ℕ → ℂ) (N : ℕ) :
    nonprimeWeightedMean ArithmeticFunction.vonMangoldt z N = (N : ℂ)⁻¹ *
      ∑ n ∈ (initialInterval N).filter (fun n => ¬n.Prime ∧ IsPrimePow n),
        (ArithmeticFunction.vonMangoldt n : ℂ) * z n :=
  nonprimeWeightedMean_eq_primePower_sum _ z N
    (fun _ hn => ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn)

end PSPrimes
