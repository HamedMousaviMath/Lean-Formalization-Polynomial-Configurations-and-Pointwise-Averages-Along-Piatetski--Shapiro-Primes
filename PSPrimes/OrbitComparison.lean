import PSPrimes.PowerSaving
import PSPrimes.Pointwise
import PSPrimes.ExternalInputs
import PSPrimes.OrbitInputs
import PSPrimes.OrbitTransference
import PSPrimes.Representatives

/-!
# Arithmetic-to-orbit comparison

The estimates in this module derive the paper's actual discrepancy rate;
that rate is not added as an external hypothesis. The orbit estimate is
proved from the finite Teräväinen input in `OrbitTransference.lean`; it is
not an independent assumption from the author's other manuscript. The deep
inputs are the named finite VN and Shao--Sun estimates, with PNT added for
the full-sequence comparison.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace PSPrimes

/-- The centered weighted average is exactly the difference of the two
original weighted averages. -/
theorem weightedAverage_discrepancy (γ : ℝ) (z : ℕ → ℂ) (N : ℕ) :
    weightedAverage (discrepancyWeight γ) z N =
      weightedAverage (sparseMangoldt γ) z N - weightedAverage ArithmeticFunction.vonMangoldt z N := by
  simp [weightedAverage, discrepancyWeight, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib, mul_sub]

/-- The zero phase gives decay of the normalized mass discrepancy. -/
theorem discrepancy_mass_tendsto (γ σ A : ℝ) (hσ : 0 < σ) (hA : 0 ≤ A)
    (r : ℕ)
    (hphase : ∀ N : ℕ, 1 ≤ N → PhaseBound r N
      (fun n => (discrepancyWeight γ n : ℂ)) (A * (N : ℝ) ^ (1 - σ))) :
    Tendsto (fun N : ℕ => (∑ n ∈ initialInterval N, discrepancyWeight γ n) / N)
      atTop (𝓝 0) := by
  have hbound (N : ℕ) :
      ‖(∑ n ∈ initialInterval N, discrepancyWeight γ n) / (N : ℝ)‖ ≤
        A * (N : ℝ) ^ (-σ) := by
    by_cases hN : N = 0
    · subst N
      simp only [initialInterval, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty, zero_div, norm_zero]
      exact mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hb := (hphase N hNpos).mass
      have hreal : ‖∑ n ∈ initialInterval N, discrepancyWeight γ n‖ ≤
          A * (N : ℝ) ^ (1 - σ) := by
        simpa only [← Complex.ofReal_sum, Complex.norm_real] using hb
      rw [norm_div, Real.norm_of_nonneg hNr.le]
      exact (div_le_div_of_nonneg_right hreal hNr.le).trans_eq
        (phase_error_normalization (N : ℝ) A σ hNr)
  have hp : Tendsto (fun N : ℕ => A * (N : ℝ) ^ (-σ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := A)).mul
        ((tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hp)

/-- Sparse weight mass follows from ordinary Mangoldt mass and zero-phase
Shao--Sun; it is not an additional arithmetic input. -/
theorem sparse_mass_tendsto_of_phase (γ σ A : ℝ) (hσ : 0 < σ) (hA : 0 ≤ A)
    (r : ℕ)
    (hphase : ∀ N : ℕ, 1 ≤ N → PhaseBound r N
      (fun n => (discrepancyWeight γ n : ℂ)) (A * (N : ℝ) ^ (1 - σ)))
    (hPNT : Tendsto (fun N : ℕ =>
      (∑ n ∈ initialInterval N, ArithmeticFunction.vonMangoldt n) / N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ initialInterval N, sparseMangoldt γ n) / N)
      atTop (𝓝 1) := by
  have hlim := hPNT.add (discrepancy_mass_tendsto γ σ A hσ hA r hphase)
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards with N
  simp only [discrepancyWeight, Finset.sum_sub_distrib]
  ring

/-- Finite arithmetic absorption of the arbitrary-weight orbit bound. The
exponents and constants are explicit and uniform in the orbit functions. -/
theorem discrepancy_orbit_L1_power_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (z : ℕ → X → ℂ) (N d K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (γ σ s A C : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs₁ : s ≤ 1) (hsσ : s ≤ σ)
    (hsmall : 8 * (1 - γ) ≤ s * (1 / (K : ℝ)))
    (hphase : PhaseBound d N (fun n => (discrepancyWeight γ n : ℂ))
      (A * (N : ℝ) ^ (1 - σ)))
    (hOR : ∀ B E : ℝ, 0 < B → 0 ≤ E →
      (∀ n ∈ initialInterval N, |discrepancyWeight γ n| ≤ B) →
      PhaseBound d N (fun n => (discrepancyWeight γ n : ℂ)) ((N : ℝ) * E) →
      Integrable (fun x => weightedAverage (discrepancyWeight γ) (fun n => z n x) N) μ ∧
      (∫ x, ‖weightedAverage (discrepancyWeight γ) (fun n => z n x) N‖ ∂μ) ≤
        C * B * ((N : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ))) :
    let t : ℝ := 1 / (K : ℝ)
    let C_B : ℝ := (γ⁻¹ + 1) / (1 - γ) * (2 : ℝ) ^ (2 * (1 - γ))
    Integrable (fun x => weightedAverage (discrepancyWeight γ) (fun n => z n x) N) μ ∧
      (∫ x, ‖weightedAverage (discrepancyWeight γ) (fun n => z n x) N‖ ∂μ) ≤
        (C * (C_B + C_B ^ (1 - t) * A ^ t)) * (N : ℝ) ^ (-(s * t) / 2) := by
  let t : ℝ := 1 / (K : ℝ)
  let B : ℝ := (γ⁻¹ + 1) * ((N + 1 : ℕ) : ℝ) ^ (1 - γ) *
    Real.log ((N + 1 : ℕ) : ℝ)
  let E : ℝ := A * (N : ℝ) ^ (1 - σ) / N
  let C_B : ℝ := (γ⁻¹ + 1) / (1 - γ) * (2 : ℝ) ^ (2 * (1 - γ))
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ht₀ : 0 < t := one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hKreal)
  have ht₁ : t ≤ 1 := (div_le_one (lt_of_lt_of_le zero_lt_one hKreal)).mpr hKreal
  have hG : 0 < γ⁻¹ + 1 := by positivity
  have heps : 0 < 1 - γ := sub_pos.mpr hγ₁
  have hBone : (1 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < N + 1)
  have hB : 0 < B := by
    dsimp [B]
    have hlog := Real.log_pos hBone
    have hpow := Real.rpow_pos_of_pos (lt_trans zero_lt_one hBone) (1 - γ)
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact div_nonneg (mul_nonneg hA (Real.rpow_nonneg hNpos.le _)) hNpos.le
  have hCB : 0 ≤ C_B := by dsimp [C_B]; positivity
  have hBpow : B ≤ C_B * (N : ℝ) ^ (2 * (1 - γ)) := by
    simpa only [B, C_B, Nat.cast_add, Nat.cast_one] using
      log_envelope_power_bound hG.le hNr heps
  have hEpow : E ≤ A * (N : ℝ) ^ (-σ) :=
    (phase_error_normalization (N : ℝ) A σ hNpos).le
  have hw : ∀ n ∈ initialInterval N, |discrepancyWeight γ n| ≤ B := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact discrepancyWeight_le_envelope hγ₀ hγ₁.le hn'.1 (by omega : n ≤ N + 1)
  have hphaseE : PhaseBound d N (fun n => (discrepancyWeight γ n : ℂ)) ((N : ℝ) * E) := by
    convert hphase using 1
    dsimp [E]
    field_simp
  obtain ⟨hint, hb⟩ := hOR B E hB hE hw hphaseE
  refine ⟨hint, hb.trans ?_⟩
  have hsave := weighted_root_saving hNr hB hE hCB hA (sub_nonneg.mpr hγ₁.le)
    ht₀.le ht₁ hs₁ hsσ hsmall hBpow hEpow
  calc
    C * B * ((N : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ)) =
      C * (B * ((N : ℝ)⁻¹ + E / B) ^ t) := by ring
    _ ≤ C * ((C_B + C_B ^ (1 - t) * A ^ t) * (N : ℝ) ^ (-(s * t) / 2)) :=
      mul_le_mul_of_nonneg_left hsave hC
    _ = _ := by ring

/-- The actual discrepancy `L¹` power saving, with degree-uniform gamma range
and saving. This is equation `e:L1-comparison`, derived from the named
external phase and finite von Neumann theorems, using the proved orbit transfer. -/
theorem ps_orbit_discrepancy_L1_gamma (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
          ∃ D : ℝ, 0 < D ∧
            ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
              ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
                (∀ i, AEStronglyMeasurable (f i) μ) →
                (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) →
                ∀ N : ℕ, 1 ≤ N →
                  Integrable (fun x =>
                    weightedAverage (sparseMangoldt γ) (fun n => orbitProduct P.polynomials T f n x) N -
                    weightedAverage ArithmeticFunction.vonMangoldt
                      (fun n => orbitProduct P.polynomials T f n x) N) μ ∧
                  (∫ x, ‖weightedAverage (sparseMangoldt γ)
                    (fun n => orbitProduct P.polynomials T f n x) N -
                    weightedAverage ArithmeticFunction.vonMangoldt
                      (fun n => orbitProduct P.polynomials T f n x) N‖ ∂μ) ≤
                    D * (N : ℝ)^(-η) := by
  obtain ⟨K, hK, hORd⟩ := (orbitVNInput_of_finiteVNInput hVN) d hd
  obtain ⟨ε₀, hε₀, hε₀₁, σ, hσ, hphase⟩ := hSS d hd
  let t : ℝ := 1 / (K : ℝ)
  let s : ℝ := min 1 σ
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have ht : 0 < t := one_div_pos.mpr hKr
  have hs : 0 < s := lt_min zero_lt_one hσ
  have hs₁ : s ≤ 1 := min_le_left _ _
  have hsσ : s ≤ σ := min_le_right _ _
  let ε : ℝ := min ε₀ (s * t / 8)
  let η : ℝ := s * t / 2
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hε₁ : ε < 1 := (min_le_left _ _).trans_lt hε₀₁
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨ε, hε, hε₁, η, hη, ?_⟩
  intro ℓ P hmax htop γ hγrange hγ₁
  have hγ₀ : 0 < γ := by linarith
  have hγSS : 1 - ε₀ < γ := by
    have hεle : ε ≤ ε₀ := min_le_left _ _
    linarith
  obtain ⟨A, hA, hphaseγ⟩ := hphase γ hγSS hγ₁
  obtain ⟨C, hC, hORP⟩ := hORd ℓ P.polynomials P.nonempty P.increasing_degrees
    P.positive_degree hmax htop
  let C_B : ℝ := (γ⁻¹ + 1) / (1 - γ) * (2 : ℝ) ^ (2 * (1 - γ))
  let D : ℝ := C * (C_B + C_B ^ (1 - t) * A ^ t)
  have heps : 0 < 1 - γ := sub_pos.mpr hγ₁
  have hCB : 0 < C_B := by dsimp [C_B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall : 8 * (1 - γ) ≤ s * (1 / (K : ℝ)) := by
    have hεle : ε ≤ s * t / 8 := min_le_right _ _
    change 8 * (1 - γ) ≤ s * t
    linarith
  refine ⟨D, hD, ?_⟩
  intro X _ μ hprob T f hf hbound N hN
  have hfin := discrepancy_orbit_L1_power_bound μ
    (fun n x => orbitProduct P.polynomials T f n x) N d K hN hK
    γ σ s A C hγ₀ hγ₁ hA.le hC.le hs₁ hsσ hsmall (hphaseγ N hN)
    (fun B E hB hE hw hp => hORP X μ hprob T f hf hbound N hN
      (discrepancyWeight γ) B E hB hE hw hp)
  simpa only [weightedAverage_discrepancy, D, C_B, η, t, neg_div] using hfin

/-- Proposition 4.1 in its exact weighted orbit form. The full-sequence
comparison is derived from the genuine `L¹` rate; no comparison conclusion
appears among the external hypotheses. -/
theorem ps_orbit_comparison_gamma (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (hPNT : PrimeNumberTheoremInput) (d : ℕ) (hd : 1 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
          ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
            ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
              (∀ i, AEStronglyMeasurable (f i) μ) →
              (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) →
              ∀ᵐ x ∂μ, Tendsto
                (fun N => weightedAverage (sparseMangoldt γ)
                  (fun n => orbitProduct P.polynomials T f n x) N -
                  weightedAverage ArithmeticFunction.vonMangoldt
                    (fun n => orbitProduct P.polynomials T f n x) N) atTop (𝓝 0) := by
  obtain ⟨ε₁, hε₁, hε₁₁, η, hη, hrate⟩ := ps_orbit_discrepancy_L1_gamma hSS hVN d hd
  obtain ⟨ε₂, hε₂, hε₂₁, σ, hσ, hphase⟩ := hSS d hd
  let ε : ℝ := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hε₀₁ : ε < 1 := (min_le_left _ _).trans_lt hε₁₁
  refine ⟨ε, hε, hε₀₁, ?_⟩
  intro ℓ P hmax htop γ hγrange hγ₁ X _ μ hprob T f hf hbound
  have hγ₀ : 0 < γ := by linarith
  have hγrange₁ : 1 - ε₁ < γ := by have : ε ≤ ε₁ := min_le_left _ _; linarith
  have hγrange₂ : 1 - ε₂ < γ := by have : ε ≤ ε₂ := min_le_right _ _; linarith
  obtain ⟨D, hD, hrateγ⟩ := hrate ℓ P hmax htop γ hγrange₁ hγ₁
  obtain ⟨A, hA, hphaseγ⟩ := hphase γ hγrange₂ hγ₁
  have hPNT' : Tendsto (fun N : ℕ =>
      (∑ n ∈ initialInterval N, ArithmeticFunction.vonMangoldt n) / N) atTop (𝓝 1) := by
    simpa only [PrimeNumberTheoremInput, div_eq_mul_inv, mul_comm] using hPNT
  have hmass := sparse_mass_tendsto_of_phase γ σ A hσ hA.le d hphaseγ hPNT'
  apply ae_weightedAverage_comparison_of_L1_decay μ (sparseMangoldt γ)
    ArithmeticFunction.vonMangoldt (fun n x => orbitProduct P.polynomials T f n x)
    (fun n => sparseMangoldt_nonneg hγ₀ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    (fun n => (ae_orbitProduct_oneBounded P.polynomials T f hbound).mono (fun x hx => hx n))
    hmass hPNT' η D hη
  · intro N
    by_cases hN : N = 0
    · subst N
      simpa [weightedAverage, initialInterval] using (integrable_zero X ℂ μ)
    · exact (hrateγ X μ hprob T f hf hbound N (Nat.pos_of_ne_zero hN)).1
  · intro N hN
    exact (hrateγ X μ hprob T f hf hbound N hN).2

/-- Proposition 4.1 with the manuscript's original parameter `c`, including
all surrounding system, measurability and essential boundedness hypotheses. -/
theorem ps_orbit_comparison (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (hPNT : PrimeNumberTheoremInput) (d : ℕ) (hd : 1 ≤ d) :
    ∃ cstar : ℝ, 1 < cstar ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ c : ℝ, 1 < c → c < cstar →
          ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
            ∀ (T : IntegerAction X μ) (f : Fin ℓ → X → ℂ),
              (∀ i, AEStronglyMeasurable (f i) μ) →
              (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) →
              ∀ᵐ x ∂μ, Tendsto
                (fun N => weightedAverage (sparseMangoldt (1 / c))
                  (fun n => orbitProduct P.polynomials T f n x) N -
                  weightedAverage ArithmeticFunction.vonMangoldt
                    (fun n => orbitProduct P.polynomials T f n x) N) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hε₁, hcomp⟩ := ps_orbit_comparison_gamma hSS hVN hPNT d hd
  let cstar : ℝ := 1 / (1 - ε)
  have hden : 0 < 1 - ε := sub_pos.mpr hε₁
  have hcstar : 1 < cstar := (lt_div_iff₀ hden).mpr (by linarith)
  refine ⟨cstar, hcstar, ?_⟩
  intro ℓ P hmax htop c hc hcup
  have hc₀ : 0 < c := lt_trans zero_lt_one hc
  have hcprod : c * (1 - ε) < 1 := (lt_div_iff₀ hden).mp hcup
  have hγ₀ : 1 - ε < 1 / c := (lt_div_iff₀ hc₀).mpr (by nlinarith)
  have hγ₁ : 1 / c < 1 := (div_lt_one hc₀).mpr hc
  exact hcomp ℓ P hmax htop (1 / c) hγ₀ hγ₁

end PSPrimes
