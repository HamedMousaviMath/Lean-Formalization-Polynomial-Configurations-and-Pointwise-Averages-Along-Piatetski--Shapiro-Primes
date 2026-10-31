import PSPrimes.PrimeDiscrepancy
import PSPrimes.FinalComparison
import PSPrimes.DiscrepancySaving

/-!
# Uniform assembly of the sparse-prime discrepancy lemma

The elementary actual-count argument is in `PrimeDiscrepancy`; this module
applies the full counting comparison to the genuine indicator functions.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace PSPrimes
attribute [local instance] Classical.propDecidable

theorem norm_setIndicator_le_one (A : Finset ℤ) (x : ℤ) :
    ‖(setIndicator A x : ℂ)‖ ≤ 1 := by
  unfold setIndicator
  split_ifs <;> simp

theorem setIndicator_vanishes_of_large_abs (N : ℕ) (A : Finset ℤ)
    (hA : A ⊆ integerInterval N) (x : ℤ) (hx : (N : ℝ) < |(x : ℝ)|) :
    setIndicator A x = 0 := by
  apply setIndicator_of_not_mem
  intro hxA
  obtain ⟨hx₁, hxN⟩ := Finset.mem_Icc.mp (hA hxA)
  have hx₀ : (0 : ℝ) ≤ x := by exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) hx₁)
  have hxNr : (x : ℝ) ≤ N := by exact_mod_cast hxN
  rw [abs_of_nonneg hx₀] at hx
  linarith

/-- Proposition 2.3 applied to actual indicator functions, uniformly in the set.
The interval range cstar and saving ξ are chosen before the polynomial family. -/
theorem comparison_on_sets (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ cstar : ℝ, 1 < cstar ∧ ∃ ξ : ℝ, 0 < ξ ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ c : ℝ, 1 < c → c < cstar →
          ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a < 1 →
            ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
              (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
              ∀ A : Finset ℤ, A ⊆ integerInterval N →
                ‖countingForm N (floorScale N Q d) Q
                  (fun j => rescale (P.polynomials j) (Q : ℤ))
                  (fun n => (discrepancyWeight (1 / c) n : ℂ))
                  (indicatorFinsupp A) (fun _ x => (setIndicator A x : ℂ))‖ ≤
                    C * (N : ℝ) ^ (-ξ) := by
  obtain ⟨cstar, hcstar, ξ, hξ, hcomp⟩ := ps_counting_comparison hSS hVN d hd
  refine ⟨cstar, hcstar, ξ, hξ, ?_⟩
  intro ℓ P hdeg htop c hc hcc
  obtain ⟨C, hC, hbound⟩ := hcomp ℓ P hdeg htop 1 le_rfl c hc hcc
  refine ⟨C, hC, ?_⟩
  intro a ha₀ ha₁
  obtain ⟨M₀, hM₀⟩ := hbound a ha₀ ha₁
  filter_upwards [eventually_floorScale_ge ha₁ d (by omega) M₀,
    eventually_ge_atTop 1] with N hscale hN
  intro Q hQ hQR A hA
  apply hM₀ N Q hN hQ hQR (hscale Q hQ hQR)
  · intro x
    simpa only [indicatorFinsupp_apply] using norm_setIndicator_le_one A x
  · intro i x
    exact norm_setIndicator_le_one A x
  · intro x hx
    rw [indicatorFinsupp_apply]
    have hh := setIndicator_vanishes_of_large_abs N A hA x (by simpa only [one_mul] using hx)
    simp [hh]
  · intro i x hx
    have hh := setIndicator_vanishes_of_large_abs N A hA x (by simpa only [one_mul] using hx)
    simp [hh]

/-- Manuscript Lemma 3.2, including uniformity in the varying modulus and
logarithmic density. The source comparison parameters and classical mass
witness are explicitly compatible data selected jointly outside this lemma.
The c-range is selected from d before the family and those source data.
No error-domination premise or original discrepancy conclusion is assumed. -/
theorem ps_prime_discrepancy (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ cstar : ℝ, 1 < cstar ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ C : ℝ, 1 ≤ C →
          (∀ i j, j ≤ d → |(P.polynomials i |>.coeff j : ℝ)| ≤ C) →
          ∀ Adiv : ℕ, ∀ p : KMTTComparisonParameters ℓ Adiv,
            ∀ mass : PrimeProgressionMassWitness p d (1 / (10 * C * (d + 1 : ℕ))),
              ∀ c : ℝ, 1 < c → c < cstar →
                ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q s : ℕ, ∀ δ : ℝ,
                  KMTTAdmissible p N Q s δ →
                  ∀ A : Finset ℤ, A ⊆ integerInterval N → (A.card : ℝ) = δ * N →
                    NoRescaledConfiguration P.polynomials Q c A →
                    p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) ≤
                      |realSetCount N (floorScale N Q d) Q
                        (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt A -
                       realModelCount N (floorScale N Q d) Q
                        (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt δ| := by
  obtain ⟨cstar₀, hcstar₀, ξ, hξ, hcomparison⟩ := comparison_on_sets hSS hVN d hd
  let cstar : ℝ := min cstar₀ (4 / 3)
  have hcstar : 1 < cstar := lt_min hcstar₀ (by norm_num)
  refine ⟨cstar, hcstar, ?_⟩
  intro ℓ P hdeg htop C hC hcoeff Adiv p mass c hc hcup
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hccomp : c < cstar₀ := hcup.trans_le (min_le_left _ _)
  have hcupper : c < (4 / 3 : ℝ) := hcup.trans_le (min_le_right _ _)
  let γ : ℝ := 1 / c
  have hγpos : 0 < γ := one_div_pos.mpr hcpos
  have hγupper : γ < 1 := (div_lt_one hcpos).mpr hc
  have hγlower : (3 / 4 : ℝ) ≤ γ := (le_div_iff₀ hcpos).mpr (by nlinarith)
  let a : ℝ := 2 * p.c₀
  have ha₀ : 0 < a := mul_pos (by norm_num) p.c₀_pos
  have ha₁ : a < 1 := by dsimp [a]; linarith [p.c₀_lt]
  obtain ⟨Ccomp, hCcomp, hcompare⟩ := hcomparison ℓ P hdeg htop c hc hccomp
  let Cerr : ℝ := sparseErrorLiftConstant γ d ℓ * (2 : ℝ) ^ (1 / 8 : ℝ)
  let η : ℝ := (1 / 8 : ℝ) / (d : ℝ)
  have hCerr : 0 < Cerr := mul_pos (sparseErrorLiftConstant_pos hγpos d ℓ)
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hη : 0 < η := by dsimp [η]; positivity
  have hhalf : 0 < p.c₁ / 2 := div_pos p.c₁_pos (by norm_num)
  have hsave := eventually_sparseCountError_power_bound hγpos hγlower ha₁ d ℓ (by omega)
  have hdomErr := eventually_powerSaving_le_density_mass
    (ν := 1 / p.C₁ ^ 2) (C := Cerr) (c := p.c₁ / 2)
    (b := mass.lowerConstant) (B := mass.exponentConstant)
    ha₁ hη hCerr hhalf mass.lowerConstant_pos mass.exponentConstant_pos (ℓ + 1)
  have hdomComp := eventually_powerSaving_le_density_mass
    (ν := 1 / p.C₁ ^ 2) (C := Ccomp) (c := p.c₁ / 2)
    (b := mass.lowerConstant) (B := mass.exponentConstant)
    ha₁ hξ hCcomp hhalf mass.lowerConstant_pos mass.exponentConstant_pos (ℓ + 1)
  have hfinal : ∀ᶠ N : ℕ in atTop, ∀ Q s : ℕ, ∀ δ : ℝ,
      KMTTAdmissible p N Q s δ →
      ∀ A : Finset ℤ, A ⊆ integerInterval N → (A.card : ℝ) = δ * N →
        NoRescaledConfiguration P.polynomials Q c A →
        p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) ≤
          |realSetCount N (floorScale N Q d) Q
            (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt A -
           realModelCount N (floorScale N Q d) Q
            (fun j => rescale (P.polynomials j) (Q : ℤ)) ArithmeticFunction.vonMangoldt δ| := by
    filter_upwards [hcompare a ha₀ ha₁, hsave, hdomErr, hdomComp,
      eventually_floorScale_pos ha₁ d (by omega), eventually_ge_atTop 1,
      eventually_ge_atTop mass.threshold] with N hcompN hsaveN hdomErrN hdomCompN hMN hN hlarge
    intro Q s δ hadmiss A hA hdensity hno
    have hdata := hadmiss
    rcases hdata with ⟨hQ, hs, hδlower, hδupper, hceil, hsupper, hQR, hsmooth, hdiv⟩
    have hδ : 0 ≤ δ := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hcard : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hM := hMN Q hQ hQR
    have hcountcomp := hcompN Q hQ hQR A hA
    have herror : sparseCountError γ d ℓ Q (floorScale N Q d) +
        Ccomp * (N : ℝ) ^ (-ξ) ≤
        p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) := by
      have hsparse : sparseCountError γ d ℓ Q (floorScale N Q d) ≤
          Cerr * (N : ℝ) ^ (-η) := by
        simpa only [Cerr, η, neg_div] using hsaveN Q hQ hQR
      have hdom₁ := hdomErrN δ hδlower
      have hdom₂ := hdomCompN δ hδlower
      have hmass := mass.full_mass N Q s δ hlarge hadmiss
      calc
        _ ≤ Cerr * (N : ℝ) ^ (-η) + Ccomp * (N : ℝ) ^ (-ξ) :=
          add_le_add_right hsparse _
        _ ≤ (p.c₁ / 2) * δ ^ (ℓ + 1) * mass.lowerConstant *
              Real.exp (-mass.exponentConstant * (Real.log N) ^ a) +
            (p.c₁ / 2) * δ ^ (ℓ + 1) * mass.lowerConstant *
              Real.exp (-mass.exponentConstant * (Real.log N) ^ a) := add_le_add hdom₁ hdom₂
        _ = p.c₁ * δ ^ (ℓ + 1) *
            (mass.lowerConstant * Real.exp (-mass.exponentConstant * (Real.log N) ^ a)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmass (mul_nonneg p.c₁_pos.le (pow_nonneg hδ _))
    have hnoγ : NoRescaledConfiguration P.polynomials Q (1 / γ) A := by
      simpa only [γ, one_div, inv_inv] using hno
    exact prime_discrepancy_finite p P C hC hd hdeg hcoeff mass N Q s δ γ
      (Ccomp * (N : ℝ) ^ (-ξ)) hN hM hδ hγpos hγupper.le hlarge hadmiss A hA hnoγ hcountcomp herror
  exact Filter.eventually_atTop.mp hfinal

end PSPrimes
