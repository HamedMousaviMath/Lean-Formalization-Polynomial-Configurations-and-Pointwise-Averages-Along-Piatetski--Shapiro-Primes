import PSPrimes.OrbitComparison
import PSPrimes.PrimePowers

/-!
# Theorem 1.2

The theorem below concerns the manuscript's actual prime and
Piatetski--Shapiro-prime averages. All original deductions, including removal
of higher prime powers, weight removal, the common limit, the gamma/c
conversion and the L∞ normalization, are proved here or in imported modules.
It is conditional exactly on four named external source specializations.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

universe u

namespace PSPrimes

attribute [local instance] Classical.propDecidable

/-- The elementary higher-prime-power mass estimate implies the normalized
nonprime residual tends to zero for every 1-bounded sample sequence. -/
theorem nonprimeWeightedMean_tendsto_zero {γ : ℝ}
    (hγ₀ : (1 / 2 : ℝ) < γ) (hγ₁ : γ ≤ 1)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hzero : ∀ n, ¬IsPrimePow n → w n = 0)
    (henv : ∀ n, w n ≤ sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n)
    (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) :
    Tendsto (nonprimeWeightedMean w z) atTop (𝓝 0) := by
  have hmass := higherPrimePowers_combined_mass_div_tendsto_zero hγ₀ hγ₁
  have hbound (N : ℕ) : ‖nonprimeWeightedMean w z N‖ ≤
      (∑ n ∈ higherPrimePowers N,
        (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n)) / (N : ℝ) := by
    have heq : nonprimeWeightedMean w z N = (N : ℂ)⁻¹ *
        ∑ n ∈ higherPrimePowers N, (w n : ℂ) * z n := by
      simpa only [higherPrimePowers, and_comm] using
        nonprimeWeightedMean_eq_primePower_sum w z N hzero
    rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
    have hs : ‖∑ n ∈ higherPrimePowers N, (w n : ℂ) * z n‖ ≤
        ∑ n ∈ higherPrimePowers N, w n := by
      simpa only [Complex.real_smul] using norm_weighted_sum_le w z (higherPrimePowers N) hw hz
    have hm : (∑ n ∈ higherPrimePowers N, w n) ≤
        ∑ n ∈ higherPrimePowers N,
          (sparseMangoldt γ n + ArithmeticFunction.vonMangoldt n) :=
      Finset.sum_le_sum (fun n _ => henv n)
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (hs.trans hm) (inv_nonneg.mpr (Nat.cast_nonneg N))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hmass)

theorem weightedAverage_one (w : ℕ → ℝ) (N : ℕ) :
    weightedAverage w (fun _ => 1) N =
      (((∑ n ∈ initialInterval N, w n) / (N : ℝ) : ℝ) : ℂ) := by
  simp [weightedAverage, Complex.ofReal_sum, Complex.ofReal_div, div_eq_mul_inv, mul_comm]

theorem selectedWeightedSum_one_normalized (S : ℕ → Prop) [DecidablePred S]
    (w : ℕ → ℝ) (N : ℕ) :
    (N : ℂ)⁻¹ * selectedWeightedSum S w (fun _ => 1) N =
      ((selectedWeightMass S w N / (N : ℝ) : ℝ) : ℂ) := by
  simp [selectedWeightedSum, selectedWeightMass, Complex.ofReal_sum,
    Complex.ofReal_div, div_eq_mul_inv, mul_comm]

/-- Exact removal of a vanishing residual preserves the weighted selected
limit. The decomposition premise is an algebraic identity, supplied by the
proved prime/nonprime decompositions, not an analytic assumption. -/
theorem selected_weighted_limit_from_decomposition
    (S : ℕ → Prop) [DecidablePred S] (w q : ℕ → ℝ) (z : ℕ → ℂ)
    (R : ℕ → ℂ) (L : ℂ)
    (hdecomp : ∀ N, weightedAverage w z N =
      (N : ℂ)⁻¹ * selectedWeightedSum S q z N + R N)
    (hw : Tendsto (fun N => weightedAverage w z N) atTop (𝓝 L))
    (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * selectedWeightedSum S q z N) atTop (𝓝 L) := by
  have hlim := hw.sub hR
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards with N
  rw [hdecomp N]
  exact add_sub_cancel_right _ _

theorem selected_mass_limit_from_decomposition
    (S : ℕ → Prop) [DecidablePred S] (w q : ℕ → ℝ) (R : ℕ → ℂ)
    (hdecomp : ∀ N, weightedAverage w (fun _ => 1) N =
      (N : ℂ)⁻¹ * selectedWeightedSum S q (fun _ => 1) N + R N)
    (hw : Tendsto (fun N : ℕ => (∑ n ∈ initialInterval N, w n) / N) atTop (𝓝 1))
    (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => selectedWeightMass S q N / N) atTop (𝓝 1) := by
  have hwC := Complex.continuous_ofReal.continuousAt.tendsto.comp hw
  simp only [Complex.ofReal_one] at hwC
  have hB : Tendsto (fun N => weightedAverage w (fun _ => 1) N) atTop (𝓝 1) := by
    simpa only [weightedAverage_one] using hwC
  have hsel := selected_weighted_limit_from_decomposition S w q (fun _ => 1) R 1 hdecomp hB hR
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hsel
  simpa only [Function.comp_apply, selectedWeightedSum_one_normalized,
    Complex.ofReal_re, Complex.one_re] using hre

/-- Manuscript Theorem 1.2, with the full probability-system and L∞
hypotheses, actual prime cutoffs and equality of the two a.e. limits.

This is conditional only on the named Shao--Sun phase specialization,
finite Teräväinen estimate, ordinary PNT, and the Mirek--Wan--Wright
ordinary-prime pointwise specialization. The needed orbit transference
from the author's other manuscript is proved internally; it is not a
premise. No original conclusion is included among these hypotheses. -/
theorem pointwiseErgodicTheorem_of_external_inputs
    (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (hPNT : PrimeNumberTheoremInput) (hMW : OrdinaryPrimePointwiseInput.{u})
    {ℓ : ℕ} (P : PolynomialFamily ℓ) : PointwiseErgodicTheorem.{u} P := by
  classical
  let iTop : Fin ℓ := ⟨ℓ - 1, by have := P.nonempty; omega⟩
  let d : ℕ := (P.polynomials iTop).natDegree
  have hd : 1 ≤ d := P.positive_degree iTop
  have hmax (i : Fin ℓ) : (P.polynomials i).natDegree ≤ d := by
    apply P.increasing_degrees.monotone
    change i.val ≤ ℓ - 1
    have := i.isLt
    omega
  have htop : ∃ i, (P.polynomials i).natDegree = d := ⟨iTop, rfl⟩
  obtain ⟨ε₁, hε₁, hε₁₁, hcomp⟩ := ps_orbit_comparison_gamma hSS hVN hPNT d hd
  obtain ⟨ε₂, hε₂, _hε₂₁, σ, hσ, hphase⟩ := hSS d hd
  let ε : ℝ := min ε₁ (min ε₂ (1 / 2))
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ (by norm_num))
  have hε₁bound : ε ≤ ε₁ := min_le_left _ _
  have hε₂bound : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hεlt : ε < 1 := hε₁bound.trans_lt hε₁₁
  let cstar : ℝ := 1 / (1 - ε)
  have hden : 0 < 1 - ε := sub_pos.mpr hεlt
  have hcstar : 1 < cstar := (lt_div_iff₀ hden).mpr (by linarith)
  refine ⟨cstar, hcstar, ?_⟩
  intro c hc hcup X _ μ hprob T f hf hbound
  have hc₀ : 0 < c := lt_trans zero_lt_one hc
  let γ : ℝ := 1 / c
  have hcprod : c * (1 - ε) < 1 := (lt_div_iff₀ hden).mp hcup
  have hγrange : 1 - ε < γ := (lt_div_iff₀ hc₀).mpr (by nlinarith)
  have hγ₁ : γ < 1 := (div_lt_one hc₀).mpr hc
  have hγ₀ : 0 < γ := one_div_pos.mpr hc₀
  have hγhalf : (1 / 2 : ℝ) < γ := by linarith
  have hγrange₁ : 1 - ε₁ < γ := by linarith
  have hγrange₂ : 1 - ε₂ < γ := by linarith
  obtain ⟨A, hA, hphaseγ⟩ := hphase γ hγrange₂ hγ₁
  have hPNT' : Tendsto (fun N : ℕ =>
      (∑ n ∈ initialInterval N, ArithmeticFunction.vonMangoldt n) / N) atTop (𝓝 1) := by
    simpa only [PrimeNumberTheoremInput, div_eq_mul_inv, mul_comm] using hPNT
  have hmassSparse := sparse_mass_tendsto_of_phase γ σ A hσ hA.le d hphaseγ hPNT'
  have hRS (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) :
      Tendsto (nonprimeWeightedMean (sparseMangoldt γ) z) atTop (𝓝 0) :=
    nonprimeWeightedMean_tendsto_zero hγhalf hγ₁.le (sparseMangoldt γ)
      (fun n => sparseMangoldt_nonneg hγ₀ n)
      (fun _ hn => sparseMangoldt_eq_zero_of_not_isPrimePow γ hn)
      (fun _ => le_add_of_nonneg_right ArithmeticFunction.vonMangoldt_nonneg) z hz
  have hRO (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) :
      Tendsto (nonprimeWeightedMean ArithmeticFunction.vonMangoldt z) atTop (𝓝 0) :=
    nonprimeWeightedMean_tendsto_zero hγhalf hγ₁.le ArithmeticFunction.vonMangoldt
      (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
      (fun _ hn => ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn)
      (fun n => le_add_of_nonneg_left (sparseMangoldt_nonneg hγ₀ n)) z hz
  have hmassS := selected_mass_limit_from_decomposition (IsPSPrime (1 / γ))
    (sparseMangoldt γ) (fun n => primeRemovalWeight γ n)
    (nonprimeWeightedMean (sparseMangoldt γ) (fun _ => 1))
    (sparse_weightedAverage_decomposition γ (fun _ => 1)) hmassSparse
    (hRS (fun _ => 1) (by intro n; simp))
  have hmassO := selected_mass_limit_from_decomposition Nat.Prime
    ArithmeticFunction.vonMangoldt (fun n => Real.log n)
    (nonprimeWeightedMean ArithmeticFunction.vonMangoldt (fun _ => 1))
    (ordinary_weightedAverage_decomposition (fun _ => 1)) hPNT'
    (hRO (fun _ => 1) (by intro n; simp))
  apply pointwiseConclusion_of_oneBounded P.polynomials c T ?_ f hf hbound
  intro g hg hgb
  obtain ⟨L, hL⟩ := hMW ℓ P.polynomials P.nonempty P.increasing_degrees
    P.positive_degree X μ hprob T g hg (fun i => ⟨1, hgb i⟩)
  have hdiff := hcomp ℓ P hmax htop γ hγrange₁ hγ₁ X μ hprob T g hg hgb
  refine ⟨L, ?_⟩
  filter_upwards [hL, hdiff, ae_orbitProduct_oneBounded P.polynomials T g hgb] with x hx hdx hzx
  let z : ℕ → ℂ := fun n => orbitProduct P.polynomials T g n x
  have hBordinary : Tendsto (fun N => weightedAverage ArithmeticFunction.vonMangoldt z N)
      atTop (𝓝 (L x)) := hx
  have hBsparse : Tendsto (fun N => weightedAverage (sparseMangoldt γ) z N)
      atTop (𝓝 (L x)) := by
    simpa only [z, zero_add, sub_add_cancel] using hdx.add hBordinary
  have hsumS := selected_weighted_limit_from_decomposition (IsPSPrime (1 / γ))
    (sparseMangoldt γ) (fun n => primeRemovalWeight γ n) z
    (nonprimeWeightedMean (sparseMangoldt γ) z) (L x)
    (sparse_weightedAverage_decomposition γ z) hBsparse (hRS z hzx)
  have hsumO := selected_weighted_limit_from_decomposition Nat.Prime
    ArithmeticFunction.vonMangoldt (fun n => Real.log n) z
    (nonprimeWeightedMean ArithmeticFunction.vonMangoldt z) (L x)
    (ordinary_weightedAverage_decomposition z) hBordinary (hRO z hzx)
  constructor
  · have hsel := selected_primes_unweighting (IsPSPrime (1 / γ))
      (fun _ hp => hp.1) γ hγ₀ hγ₁.le z (L x) hmassS hsumS
    change Tendsto (fun N => selectedAverage (IsPSPrime (1 / γ)) z N) atTop (𝓝 (L x)) at hsel
    simpa only [γ, one_div, inv_inv, z] using hsel
  · apply selected_primes_unweighting Nat.Prime (fun _ hp => hp) 1 zero_lt_one le_rfl z (L x)
    · simpa only [primeRemovalWeight_one] using hmassO
    · simpa only [primeRemovalWeight_one] using hsumO

end PSPrimes
