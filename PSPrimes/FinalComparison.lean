import PSPrimes.AsymptoticScales

/-!
# Degree-uniform PS-prime counting comparison

The saving and gamma range below are chosen before the polynomial family.
The implied constant is chosen before the subpower exponent a; only the
eventual threshold may depend on a. The only analytic inputs are the explicitly
quoted Shao--Sun and fixed-family finite VN theorems.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace PSPrimes

/-- Gamma-form of manuscript Proposition 2.3, with the original counting form,
the exact floor scale, all spatial support hypotheses and degree-only saving.
Its eventual-in-N formulation implies the stated sufficiently-large-M version
because `floorScale_le_length` proves M≤N. -/
theorem ps_counting_comparison_gamma (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ ξ : ℝ, 0 < ξ ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ C₀ : ℝ, 1 ≤ C₀ →
          ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
            ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, a < 1 →
              ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
                (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
                ∀ (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ),
                  (∀ x, ‖f₀ x‖ ≤ 1) → (∀ i x, ‖f i x‖ ≤ 1) →
                  (∀ x : ℤ, C₀ * (N : ℝ) < |(x : ℝ)| → f₀ x = 0) →
                  (∀ i (x : ℤ), C₀ * (N : ℝ) < |(x : ℝ)| → f i x = 0) →
                  ‖countingForm N (floorScale N Q d) Q
                      (fun i => rescale (P.polynomials i) (Q : ℤ))
                      (fun n => (discrepancyWeight γ n : ℂ)) f₀ f‖ ≤
                    C * (N : ℝ) ^ (-ξ) := by
  obtain ⟨K, hK, hVNd⟩ := hVN d hd
  obtain ⟨ε₀, hε₀, hε₀₁, σ, hσ, hphase⟩ := progressionPhase_of_shaoSun hSS d hd
  let t : ℝ := 1 / (K : ℝ)
  let s : ℝ := min 1 σ
  have hKreal : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have ht : 0 < t := one_div_pos.mpr hKreal
  have hs : 0 < s := lt_min zero_lt_one hσ
  have hs₁ : s ≤ 1 := min_le_left _ _
  have hsσ : s ≤ σ := min_le_right _ _
  let ε : ℝ := min ε₀ (s * t / 8)
  let ξ : ℝ := (s * t / 4) / (d : ℝ)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hε₁ : ε < 1 := (min_le_left _ _).trans_lt hε₀₁
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  refine ⟨ε, hε, hε₁, ξ, hξ, ?_⟩
  intro ℓ P hmax htop C₀ hC₀ γ hγ₀ hγ₁
  have hγ : 0 < γ := by linarith
  have hγSS : 1 - ε₀ < γ := by
    have h := min_le_left ε₀ (s * t / 8)
    change ε ≤ ε₀ at h
    linarith
  have hsmall : 8 * (1 - γ) ≤ s * t := by
    have h := min_le_right ε₀ (s * t / 8)
    change ε ≤ s * t / 8 at h
    linarith
  obtain ⟨A, hA, hphaseγ⟩ := hphase γ hγSS hγ₁
  let C₁ : ℝ := C₀ * (2 : ℝ) ^ d
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hC₁ : 1 ≤ C₁ := by
    have h := mul_le_mul_of_nonneg_left htwo (show 0 ≤ C₀ by linarith)
    exact hC₀.trans (by simpa only [mul_one] using h)
  obtain ⟨C_VN, hC_VN, hVNP⟩ := hVNd ℓ P.polynomials P.nonempty
    P.increasing_degrees P.positive_degree hmax htop C₁ hC₁
  let C_B : ℝ := (γ⁻¹ + 1) / (1 - γ) * (2 : ℝ) ^ (2 * (1 - γ))
  let C : ℝ := C_VN * (C_B + C_B ^ (1 - t) * A ^ t) * (2 : ℝ) ^ (s * t / 4)
  have hCB : 0 < C_B := by
    dsimp [C_B]
    have he : 0 < 1 - γ := sub_pos.mpr hγ₁
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a ha
  have hδ : 0 < s * t / 8 := by positivity
  filter_upwards [eventually_liftedScale_parameters ha hδ d (by omega),
    eventually_ge_atTop 1] with N hparameters hN
  intro Q hQ hQrange f₀ f hf₀ hf hs₀ hsf
  obtain ⟨hM, hLlower, hQpow⟩ := hparameters Q hQ hQrange
  have hQpos : 0 < Q := by omega
  have hq : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQpos)
  have hqabs : |((Q : ℤ) : ℝ)| = (Q : ℝ) := by simp
  have hscale := dilated_support_scale_le N Q d hQpos (by omega) hM
    (show 0 ≤ C₀ by linarith)
  have hs₀lift : ∀ x : ℤ, C₁ * (liftedScale N Q d : ℝ) ^ d < |(x : ℝ)| →
      liftFinsupp (Q : ℤ) hq f₀ x = 0 := by
    intro x hx
    apply liftFinsupp_vanishes (Q : ℤ) hq f₀ (C₀ * (N : ℝ)) hs₀ x
    calc
      |((Q : ℤ) : ℝ)| * (C₀ * (N : ℝ)) = (Q : ℝ) * C₀ * (N : ℝ) := by rw [hqabs]; ring
      _ ≤ C₁ * (liftedScale N Q d : ℝ) ^ d := hscale
      _ < |(x : ℝ)| := hx
  have hsflift : ∀ i (x : ℤ), C₁ * (liftedScale N Q d : ℝ) ^ d < |(x : ℝ)| →
      liftFunction (Q : ℤ) (f i) x = 0 := by
    intro i x hx
    apply liftFunction_vanishes (Q : ℤ) (f i) (C₀ * (N : ℝ)) (hsf i) x
    calc
      |((Q : ℤ) : ℝ)| * (C₀ * (N : ℝ)) = (Q : ℝ) * C₀ * (N : ℝ) := by rw [hqabs]; ring
      _ ≤ C₁ * (liftedScale N Q d : ℝ) ^ d := hscale
      _ < |(x : ℝ)| := hx
  have hLpos : 1 ≤ liftedScale N Q d := by
    change 1 ≤ Q * floorScale N Q d
    nlinarith
  have hVNinstance : ∀ (θ : ℕ → ℂ) (E : ℝ),
      (∀ n ∈ initialInterval (liftedScale N Q d), ‖θ n‖ ≤ 1) →
      0 ≤ E → PhaseBound d (liftedScale N Q d) θ ((liftedScale N Q d : ℝ) * E) →
      ‖polynomialForm (liftedScale N Q d) d P.polynomials θ
          (liftFinsupp (Q : ℤ) hq f₀) (fun i => liftFunction (Q : ℤ) (f i))‖ ≤
        C_VN * ((liftedScale N Q d : ℝ)⁻¹ + E) ^ (1 / (K : ℝ)) := by
    intro θ E hθ hE hp
    apply hVNP (liftedScale N Q d) hLpos θ
      (liftFinsupp (Q : ℤ) hq f₀) (fun i => liftFunction (Q : ℤ) (f i)) E hθ
    · intro x
      exact norm_liftFinsupp_le (Q : ℤ) hq f₀ zero_le_one hf₀ x
    · intro i x
      exact norm_liftFunction_le (Q : ℤ) (f i) zero_le_one (hf i) x
    · exact hs₀lift
    · exact hsflift
    · exact hE
    · exact hp
  have hphaseNM := hphaseγ Q (floorScale N Q d) hQ hM
  have hsave := ps_counting_comparison_power_bound N Q d K (by omega) hQpos
    (by omega) hM hK P.polynomials P.zero_constant γ σ s A C_VN hγ hγ₁ hA.le hC_VN.le
    hs hs₁ hsσ hsmall hQpow f₀ f hVNinstance hphaseNM
  simpa only [C, C_B, ξ, t, neg_div] using hsave

/-- Manuscript Proposition 2.3 with its original c-parameter and its
"sufficiently large M" threshold. The constants c* and ξ depend only on d;
the implied constant is chosen before a, while the M threshold may depend on a.
This conclusion is conditional exactly on the two quoted analytic inputs. -/
theorem ps_counting_comparison (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ cstar : ℝ, 1 < cstar ∧ ∃ ξ : ℝ, 0 < ξ ∧
      ∀ (ℓ : ℕ) (P : PolynomialFamily ℓ),
        (∀ i, (P.polynomials i).natDegree ≤ d) →
        (∃ i, (P.polynomials i).natDegree = d) →
        ∀ C₀ : ℝ, 1 ≤ C₀ →
          ∀ c : ℝ, 1 < c → c < cstar →
            ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a < 1 →
              ∃ M₀ : ℕ, ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q →
                (Q : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ a) →
                M₀ ≤ floorScale N Q d →
                ∀ (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ),
                  (∀ x, ‖f₀ x‖ ≤ 1) → (∀ i x, ‖f i x‖ ≤ 1) →
                  (∀ x : ℤ, C₀ * (N : ℝ) < |(x : ℝ)| → f₀ x = 0) →
                  (∀ i (x : ℤ), C₀ * (N : ℝ) < |(x : ℝ)| → f i x = 0) →
                  ‖countingForm N (floorScale N Q d) Q
                      (fun i => rescale (P.polynomials i) (Q : ℤ))
                      (fun n => (discrepancyWeight (1 / c) n : ℂ)) f₀ f‖ ≤
                    C * (N : ℝ) ^ (-ξ) := by
  obtain ⟨ε, hε, hε₁, ξ, hξ, hcomparison⟩ := ps_counting_comparison_gamma hSS hVN d hd
  let cstar : ℝ := 1 / (1 - ε)
  have hden : 0 < 1 - ε := sub_pos.mpr hε₁
  have hcstar : 1 < cstar := (lt_div_iff₀ hden).mpr (by linarith)
  refine ⟨cstar, hcstar, ξ, hξ, ?_⟩
  intro ℓ P hmax htop C₀ hC₀ c hc hcup
  have hc₀ : 0 < c := lt_trans zero_lt_one hc
  have hcprod : c * (1 - ε) < 1 := (lt_div_iff₀ hden).mp hcup
  have hγ₀ : 1 - ε < 1 / c := (lt_div_iff₀ hc₀).mpr (by nlinarith)
  have hγ₁ : 1 / c < 1 := (div_lt_one hc₀).mpr hc
  obtain ⟨C, hC, hCbound⟩ := hcomparison ℓ P hmax htop C₀ hC₀ (1 / c) hγ₀ hγ₁
  refine ⟨C, hC, ?_⟩
  intro a _ha₀ ha₁
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hCbound a ha₁)
  refine ⟨max 1 N₀, ?_⟩
  intro N Q hN hQ hQrange hM f₀ f hf₀ hf hs₀ hsf
  have hN₀le : N₀ ≤ N :=
    (le_max_right 1 N₀).trans
      (hM.trans (floorScale_le_length N Q d hN hQ (by omega)))
  exact hN₀ N hN₀le Q hQ hQrange f₀ f hf₀ hf hs₀ hsf

end PSPrimes
