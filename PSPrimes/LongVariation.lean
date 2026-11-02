import PSPrimes.OrbitComparison
import PSPrimes.Variation
import PSPrimes.Lacunary
import PSPrimes.VariationHomogeneity

/-!
# The revised manuscript's lacunary variation corollary

The new external premise is the bounded probability-space specialization of
Mirek--Wan--Wright Theorem 1.1(iv), not a consequence of the existing
pointwise input. The discrepancy rate and its variation transfer are proved.
The true infinite seminorm is used throughout, with extended nonnegative
integrals, so divergent variation cannot satisfy the bound by convention.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

universe u

namespace PSPrimes

/-- MW-V: the unit-L∞ probability-space specialization of MWW Theorem
1.1(iv), equation (1.5). The source controls the stronger variation norm.
The finite-Lq embedding (choose q_i=2ℓ), L²-to-L¹ estimate, and source
specialization are explicitly external bridges in docs/ASSUMPTIONS.md.
The constant precedes the lacunary sequence, system and functions.
`orbitProduct` evaluates the actual shifted polynomials P_i(n-1). -/
def OrdinaryPrimeVariationInput : Prop :=
  ∀ (ℓ : ℕ) (P : Fin ℓ → Polynomial ℤ),
    0 < ℓ → StrictMono (fun i => (P i).natDegree) →
    (∀ i, 1 ≤ (P i).natDegree) →
    ∀ r : ℝ, 2 < r → ∀ rho : ℝ, 1 < rho →
      ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ → ℕ, 1 ≤ N 0 →
          (∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) →
          ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
            ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
              (∀ i, AEStronglyMeasurable (f i) μ) →
              (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) →
              (∫⁻ x, rVariation r (fun j =>
                weightedAverage ArithmeticFunction.vonMangoldt
                  (fun n => orbitProduct P T f n x) (N j)) ∂μ) ≤ ENNReal.ofReal C

/-- Uniform transfer of an actual L¹ power saving to infinite lacunary
variation. This is the substantive new deduction, before arithmetic input.
It holds for every r≥1; r>2 is needed only by the ordinary-prime theorem. -/
theorem lacunary_variation_perturbation_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {r rho η D : ℝ} (hr : 1 ≤ r) (hrho : 1 < rho)
    (hη : 0 < η) (hD : 0 ≤ D)
    (N : ℕ → ℕ) (hN : 1 ≤ N 0)
    (hstep : ∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ))
    (a b : ℕ → X → ℂ)
    (hint : ∀ n, 1 ≤ n → Integrable (fun x => a n x - b n x) μ)
    (hdecay : ∀ n, 1 ≤ n →
      (∫ x, ‖a n x - b n x‖ ∂μ) ≤ D * (n : ℝ) ^ (-η)) :
    (∫⁻ x, rVariation r (fun j => a (N j) x - b (N j) x) ∂μ) ≤
      ENNReal.ofReal (2 * D * (1 - rho ^ (-η))⁻¹) := by
  have hpos := lacunary_positive hrho N hN hstep
  have hmeas (j : ℕ) := (hint (N j) (hpos j)).aestronglyMeasurable
  calc
    (∫⁻ x, rVariation r (fun j => a (N j) x - b (N j) x) ∂μ) ≤
        2 * ∑' j, ∫⁻ x, ‖a (N j) x - b (N j) x‖ₑ ∂μ :=
      lintegral_rVariation_le_two_tsum μ hr _ hmeas
    _ ≤ 2 * ∑' j, ENNReal.ofReal (D * (N j : ℝ) ^ (-η)) := by
      gcongr with j
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hint (N j) (hpos j))]
      exact ENNReal.ofReal_le_ofReal (hdecay (N j) (hpos j))
    _ = 2 * (ENNReal.ofReal D * ∑' j, ENNReal.ofReal ((N j : ℝ) ^ (-η))) := by
      simp only [ENNReal.ofReal_mul hD, ENNReal.tsum_mul_left]
    _ ≤ 2 * (ENNReal.ofReal D * ENNReal.ofReal ((1 - rho ^ (-η))⁻¹)) := by
      gcongr
      exact lacunary_rpow_tsum_ennreal_le hrho hη N hN hstep
    _ = ENNReal.ofReal (2 * D * (1 - rho ^ (-η))⁻¹) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hD),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      ring

/-- The unit-input estimate, with a degree-only admissible gamma range.
Neither the gamma range nor its saving depends on r or the lacunarity.
The bound constant precedes every system, sequence and observable. -/
theorem ps_lacunary_variation_gamma
    (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (hMW : OrdinaryPrimeVariationInput.{u}) (d : ℕ) (hd : 1 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
          ∀ r : ℝ, 2 < r → ∀ rho : ℝ, 1 < rho →
            ∃ C : ℝ, 0 < C ∧
              ∀ N : ℕ → ℕ, 1 ≤ N 0 →
                (∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) →
                ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
                  ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
                    (∀ i, AEStronglyMeasurable (f i) μ) →
                    (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) →
                    (∫⁻ x, rVariation r (fun j =>
                      weightedAverage (sparseMangoldt γ)
                        (fun n => orbitProduct P.polynomials T f n x) (N j)) ∂μ) ≤
                      ENNReal.ofReal C := by
  obtain ⟨ε, hε, hε₁, η, hη, hdecay⟩ := ps_orbit_discrepancy_L1_gamma hSS hVN d hd
  refine ⟨ε, hε, hε₁, ?_⟩
  intro ℓ P hmax htop γ hγ hγ₁ r hr rho hrho
  obtain ⟨D, hD, hDP⟩ := hdecay ℓ P hmax htop γ hγ hγ₁
  obtain ⟨C₀, hC₀, hordinary⟩ := hMW ℓ P.polynomials P.nonempty
    P.increasing_degrees P.positive_degree r hr rho hrho
  let S : ℝ := (1 - rho ^ (-η))⁻¹
  have hS : 0 < S := inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hrho (by linarith)))
  refine ⟨C₀ + 2 * D * S, by positivity, ?_⟩
  intro N hN hstep X _ μ hprob T f hf hb
  letI : IsProbabilityMeasure μ := hprob
  let a : ℕ → X → ℂ := fun n x => weightedAverage (sparseMangoldt γ)
    (fun k => orbitProduct P.polynomials T f k x) n
  let b : ℕ → X → ℂ := fun n x => weightedAverage ArithmeticFunction.vonMangoldt
    (fun k => orbitProduct P.polynomials T f k x) n
  have herr := lacunary_variation_perturbation_bound μ (by linarith : 1 ≤ r)
    hrho hη hD.le N hN hstep a b
    (fun n hn => (hDP X μ hprob T f hf hb n hn).1)
    (fun n hn => (hDP X μ hprob T f hf hb n hn).2)
  have hm (j : ℕ) : AEStronglyMeasurable (fun x => a (N j) x - b (N j) x) μ :=
    ((weighted_orbitAverage_integrable P.polynomials T f hf hb (sparseMangoldt γ) (N j)).sub
      (weighted_orbitAverage_integrable P.polynomials T f hf hb
        ArithmeticFunction.vonMangoldt (N j))).aestronglyMeasurable
  have htri (x : X) : rVariation r (fun j => a (N j) x) ≤
      rVariation r (fun j => a (N j) x - b (N j) x) +
        rVariation r (fun j => b (N j) x) := by
    convert rVariation_add_le (by linarith : 1 ≤ r)
      (fun j => a (N j) x - b (N j) x) (fun j => b (N j) x) using 1
    simp
  calc
    (∫⁻ x, rVariation r (fun j => a (N j) x) ∂μ) ≤
        ∫⁻ x, rVariation r (fun j => a (N j) x - b (N j) x) +
          rVariation r (fun j => b (N j) x) ∂μ := lintegral_mono htri
    _ = (∫⁻ x, rVariation r (fun j => a (N j) x - b (N j) x) ∂μ) +
        ∫⁻ x, rVariation r (fun j => b (N j) x) ∂μ :=
      lintegral_add_left' (aemeasurable_rVariation μ r _ hm) _
    _ ≤ ENNReal.ofReal (2 * D * S) + ENNReal.ofReal C₀ :=
      add_le_add herr (hordinary N hN hstep X μ hprob T f hf hb)
    _ = ENNReal.ofReal (C₀ + 2 * D * S) := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * D * S) hC₀.le, add_comm]

/-- Revised manuscript Corollary 4.2 (`c:long-variation`).

The output is exactly the L¹ norm of the infinite variation seminorm of
the actual sparse-von-Mangoldt weighted averages. `MemLp ... ∞` expresses
the manuscript's L∞ hypothesis, including arbitrary measurable
representatives; the product is their exact essential norms. Cutoffs are
indexed from zero (the manuscript's N_{j+1}), with no restriction on the
positive first cutoff. c* precedes c,r,rho, and C precedes the sequence,
probability system and functions. No PNT or ordinary pointwise-convergence
input is needed for this additional corollary. -/
theorem lacunary_variation_of_external_inputs
    (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (hMW : OrdinaryPrimeVariationInput.{u})
    {ℓ : ℕ} (P : PolynomialFamily ℓ) :
    ∃ cstar : ℝ, 1 < cstar ∧
      ∀ c : ℝ, 1 < c → c < cstar →
        ∀ r : ℝ, 2 < r → ∀ rho : ℝ, 1 < rho →
          ∃ C : ℝ, 0 < C ∧
            ∀ N : ℕ → ℕ, 1 ≤ N 0 →
              (∀ j, rho * (N j : ℝ) ≤ (N (j + 1) : ℝ)) →
              ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
                ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
                  (∀ i, MemLp (f i) ∞ μ) →
                  (∫⁻ x, rVariation r (fun j =>
                    weightedAverage (sparseMangoldt (1 / c))
                      (fun n => orbitProduct P.polynomials T f n x) (N j)) ∂μ) ≤
                    ENNReal.ofReal C * ∏ i, eLpNorm (f i) ∞ μ := by
  let iTop : Fin ℓ := ⟨ℓ - 1, by have := P.nonempty; omega⟩
  let d : ℕ := (P.polynomials iTop).natDegree
  have hd : 1 ≤ d := P.positive_degree iTop
  have hmax (i : Fin ℓ) : (P.polynomials i).natDegree ≤ d := by
    apply P.increasing_degrees.monotone
    change i.val ≤ ℓ - 1
    have := i.isLt
    omega
  have htop : ∃ i, (P.polynomials i).natDegree = d := ⟨iTop, rfl⟩
  obtain ⟨ε, hε, hε₁, hgamma⟩ := ps_lacunary_variation_gamma hSS hVN hMW d hd
  have hden : 0 < 1 - ε := sub_pos.mpr hε₁
  refine ⟨1 / (1 - ε), (lt_div_iff₀ hden).mpr (by linarith), ?_⟩
  intro c hc hcup r hr rho hrho
  have hc₀ : 0 < c := by linarith
  have hγ : 1 - ε < 1 / c := (lt_div_iff₀ hc₀).mpr
    (by have := (lt_div_iff₀ hden).mp hcup; nlinarith)
  have hγ₁ : 1 / c < 1 := (div_lt_one hc₀).mpr hc
  obtain ⟨C, hC, hunit⟩ := hgamma ℓ P hmax htop (1 / c) hγ hγ₁ r hr rho hrho
  refine ⟨C, hC, ?_⟩
  intro N hN hstep X _ μ hprob T f hf
  exact orbit_variation_bound_eLpNorm_of_oneBounded P.polynomials T
    (sparseMangoldt (1 / c)) N (by linarith : 0 < r) (ENNReal.ofReal C)
    (hunit N hN hstep X μ hprob T) f hf

end PSPrimes
