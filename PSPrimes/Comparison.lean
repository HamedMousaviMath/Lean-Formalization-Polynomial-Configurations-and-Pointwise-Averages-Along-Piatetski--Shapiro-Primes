import PSPrimes.Homogeneity
import PSPrimes.Lifting
import PSPrimes.Progressions
import PSPrimes.ExceptionalTerms

/-!
# Finite fixed-family comparison

The change of variables and homogeneity in Proposition 2.3 are checked here.
The analytic theorem is an explicit input for arbitrary bounded weights;
it is not an assumption about the target Piatetski--Shapiro comparison.
The final subpower-modulus asymptotics are a separate obligation.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

theorem countingForm_comparison_finite {ℓ : ℕ}
    (N Q M d K : ℕ) (hQ : 0 < Q) (hM : 0 < M)
    (P : Fin ℓ → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ) (C : ℝ)
    (hVN : ∀ (θ : ℕ → ℂ) (E : ℝ),
      (∀ n ∈ initialInterval (Q * M), ‖θ n‖ ≤ 1) →
      0 ≤ E → PhaseBound d (Q * M) θ (((Q * M : ℕ) : ℝ) * E) →
      ‖polynomialForm (Q * M) d P θ
          (liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀)
          (fun i => liftFunction (Q : ℤ) (f i))‖ ≤
        C * ((((Q * M : ℕ) : ℝ))⁻¹ + E) ^ (1 / (K : ℝ)))
    (B E : ℝ) (hB : 0 < B) (hE : 0 ≤ E)
    (hw : ∀ n ∈ initialInterval (Q * M), ‖w (n + 1)‖ ≤ B)
    (hphase : PhaseBound d M (fun y => w (Q * y + 1))
      (((Q * M : ℕ) : ℝ) * E)) :
    ‖countingForm N M Q (fun i => rescale (P i) (Q : ℤ)) w f₀ f‖ ≤
      (((Q * M : ℕ) : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹) *
        (B * C * ((((Q * M : ℕ) : ℝ))⁻¹ + E / B) ^ (1 / (K : ℝ))) := by
  have hweight : ∀ n ∈ initialInterval (Q * M), ‖liftWeight Q w n‖ ≤ B := by
    intro n hn
    exact norm_liftWeight_le Q w hB.le n (hw n hn)
  have hbound := homogeneous_polynomialForm_bound (Q * M) d K P
    (liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀)
    (fun i => liftFunction (Q : ℤ) (f i)) C hVN B E hB hE (liftWeight Q w)
    hweight (hphase.liftWeight hQ)
  rw [countingForm_lift N Q M d hQ hM P hP w f₀ f, norm_mul]
  have hnorm :
      ‖((Q * M : ℕ) : ℂ) ^ (d + 1) * ((N : ℂ) * (M : ℂ))⁻¹‖ =
        ((Q * M : ℕ) : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹ := by
    simp [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)).trans_eq (by rw [hnorm])

/-- The finite comparison deduced directly from the external finite von Neumann
input. `K` and `C` are chosen before Q, N, M and all spatial functions, so the
result retains the fixed-family uniformity used by the paper. The two lifted
support hypotheses are explicit finite data, not further analytic inputs. -/
theorem FiniteVNInput.comparison (hinput : FiniteVNInput)
    (d ℓ : ℕ) (hd : 1 ≤ d) (P : Fin ℓ → Polynomial ℤ)
    (hℓ : 0 < ℓ) (hmono : StrictMono (fun i => (P i).natDegree))
    (hpos : ∀ i, 1 ≤ (P i).natDegree)
    (hmax : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (hP : ∀ i, (P i).coeff 0 = 0) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N Q M : ℕ) (hQ : 0 < Q) (_hM : 0 < M)
        (w : ℕ → ℂ) (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ),
        (∀ x, ‖f₀ x‖ ≤ 1) → (∀ i x, ‖f i x‖ ≤ 1) →
        (∀ x : ℤ, C₀ * ((Q * M : ℕ) : ℝ) ^ d < |(x : ℝ)| →
          liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀ x = 0) →
        (∀ i (x : ℤ), C₀ * ((Q * M : ℕ) : ℝ) ^ d < |(x : ℝ)| →
          liftFunction (Q : ℤ) (f i) x = 0) →
        ∀ B E : ℝ, 0 < B → 0 ≤ E →
          (∀ n ∈ initialInterval (Q * M), ‖w (n + 1)‖ ≤ B) →
          PhaseBound d M (fun y => w (Q * y + 1)) (((Q * M : ℕ) : ℝ) * E) →
          ‖countingForm N M Q (fun i => rescale (P i) (Q : ℤ)) w f₀ f‖ ≤
            (((Q * M : ℕ) : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹) *
              (B * C * ((((Q * M : ℕ) : ℝ))⁻¹ + E / B) ^ (1 / (K : ℝ))) := by
  obtain ⟨K, hK, hVN⟩ := hinput d hd
  obtain ⟨C, hC, hVN⟩ := hVN ℓ P hℓ hmono hpos hmax htop C₀ hC₀
  refine ⟨K, hK, C, hC, ?_⟩
  intro N Q M hQ hM w f₀ f hf₀ hf hs₀ hs B E hB hE hw hp
  apply countingForm_comparison_finite N Q M d K hQ hM P hP w f₀ f C ?_
    B E hB hE hw hp
  intro θ E hθ hE hp
  apply hVN (Q * M) (Nat.succ_le_of_lt (Nat.mul_pos hQ hM)) θ
    (liftFinsupp (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ)) f₀)
    (fun i => liftFunction (Q : ℤ) (f i)) E hθ
  · intro x
    exact norm_liftFinsupp_le (Q : ℤ) (by exact_mod_cast (Nat.ne_of_gt hQ))
      f₀ zero_le_one hf₀ x
  · intro i x
    exact norm_liftFunction_le (Q : ℤ) (f i) zero_le_one (hf i) x
  · exact hs₀
  · exact hs
  · exact hE
  · exact hp

/-- The actual PS-prime discrepancy counting form, with every finite
normalization and the size of the discrepancy weight made explicit.
The original spatial supports have radius R; the finite scale inequality
`Q*R ≤ C₀ L^d` is retained explicitly. This is the quantitative finite estimate
before the subpower-modulus asymptotic absorption in Proposition 2.3. -/
theorem ps_counting_comparison_raw (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (d ℓ : ℕ) (hd : 1 ≤ d) (P : Fin ℓ → Polynomial ℤ)
    (hℓ : 0 < ℓ) (hmono : StrictMono (fun i => (P i).natDegree))
    (hpos : ∀ i, 1 ≤ (P i).natDegree)
    (hmax : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (hP : ∀ i, (P i).coeff 0 = 0) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ σ : ℝ, 0 < σ ∧
        ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
          ∃ A : ℝ, 0 < A ∧
            ∀ (N Q M : ℕ) (_hQ : 0 < Q) (_hM : 0 < M) (R : ℝ)
              (f₀ : ℤ →₀ ℂ) (f : Fin ℓ → ℤ → ℂ),
              (∀ x, ‖f₀ x‖ ≤ 1) → (∀ i x, ‖f i x‖ ≤ 1) →
              (Q : ℝ) * R ≤ C₀ * ((Q * M : ℕ) : ℝ) ^ d →
              (∀ x : ℤ, R < |(x : ℝ)| → f₀ x = 0) →
              (∀ i (x : ℤ), R < |(x : ℝ)| → f i x = 0) →
              let L : ℕ := Q * M
              let B : ℝ := (γ⁻¹ + 1) * ((L + 1 : ℕ) : ℝ) ^ (1 - γ) *
                Real.log ((L + 1 : ℕ) : ℝ)
              let E : ℝ := A * (L : ℝ) ^ (1 - σ) / L
              ‖countingForm N M Q (fun i => rescale (P i) (Q : ℤ))
                  (fun n => (discrepancyWeight γ n : ℂ)) f₀ f‖ ≤
                ((L : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹) *
                  (B * C * ((L : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ))) := by
  obtain ⟨K, hK, C, hC, hcompare⟩ :=
    hVN.comparison d ℓ hd P hℓ hmono hpos hmax htop hP C₀ hC₀
  obtain ⟨ε, hε, hε₁, σ, hσ, hphase⟩ := progressionPhase_of_shaoSun hSS d hd
  refine ⟨K, hK, C, hC, ε, hε, hε₁, σ, hσ, ?_⟩
  intro γ hγ₀ hγ₁
  obtain ⟨A, hA, hphase⟩ := hphase γ hγ₀ hγ₁
  refine ⟨A, hA, ?_⟩
  intro N Q M hQ hM R f₀ f hf₀ hf hscale hs₀ hs
  let L : ℕ := Q * M
  let B : ℝ := (γ⁻¹ + 1) * ((L + 1 : ℕ) : ℝ) ^ (1 - γ) *
    Real.log ((L + 1 : ℕ) : ℝ)
  let E : ℝ := A * (L : ℝ) ^ (1 - σ) / L
  change ‖countingForm N M Q (fun i => rescale (P i) (Q : ℤ))
    (fun n => (discrepancyWeight γ n : ℂ)) f₀ f‖ ≤
    ((L : ℝ) ^ (d + 1) * ((N : ℝ) * (M : ℝ))⁻¹) *
      (B * C * ((L : ℝ)⁻¹ + E / B) ^ (1 / (K : ℝ)))
  have hLnat : 0 < L := Nat.mul_pos hQ hM
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hLone : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < L + 1)
  have hγ : 0 < γ := by linarith
  have hq : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hqabs : |((Q : ℤ) : ℝ)| = (Q : ℝ) := by simp
  have hB : 0 < B := by
    dsimp [B]
    have hlog := Real.log_pos hLone
    have hpow := Real.rpow_pos_of_pos (lt_trans zero_lt_one hLone) (1 - γ)
    have hinv := inv_pos.mpr hγ
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact div_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hL.le _)) hL.le
  have hs₀' : ∀ x : ℤ, C₀ * ((Q * M : ℕ) : ℝ) ^ d < |(x : ℝ)| →
      liftFinsupp (Q : ℤ) hq f₀ x = 0 := by
    intro x hx
    apply liftFinsupp_vanishes (Q : ℤ) hq f₀ R hs₀ x
    rw [hqabs]
    exact lt_of_le_of_lt hscale hx
  have hs' : ∀ i (x : ℤ), C₀ * ((Q * M : ℕ) : ℝ) ^ d < |(x : ℝ)| →
      liftFunction (Q : ℤ) (f i) x = 0 := by
    intro i x hx
    apply liftFunction_vanishes (Q : ℤ) (f i) R (hs i) x
    rw [hqabs]
    exact lt_of_le_of_lt hscale hx
  have hw : ∀ n ∈ initialInterval (Q * M),
      ‖(discrepancyWeight γ (n + 1) : ℂ)‖ ≤ B := by
    intro n hn
    have hnL : n + 1 ≤ L + 1 :=
      Nat.add_le_add_right (Finset.mem_Icc.mp hn).2 1
    simpa only [Complex.norm_real, Real.norm_eq_abs, B] using
      discrepancyWeight_le_envelope hγ hγ₁.le (by omega : 1 ≤ n + 1) hnL
  have hp : PhaseBound d M (fun y => (discrepancyWeight γ (Q * y + 1) : ℂ))
      (((Q * M : ℕ) : ℝ) * E) := by
    intro φ hφ
    calc
      _ ≤ A * (L : ℝ) ^ (1 - σ) :=
        hphase Q M (Nat.succ_le_of_lt hQ) (Nat.succ_le_of_lt hM) φ hφ
      _ = ((Q * M : ℕ) : ℝ) * E := by
        dsimp [E, L]
        field_simp [hL.ne']
  exact hcompare N Q M hQ hM (fun n => (discrepancyWeight γ n : ℂ)) f₀ f
    hf₀ hf hs₀' hs' B E hB hE hw hp

end PSPrimes
