import PSPrimes.RecurrenceConstruction
import PSPrimes.FinalPrimeDiscrepancy

noncomputable section
namespace PSPrimes

/-- The actual first main theorem, for explicitly paired source witnesses.
The KMTT comparison constant is shared with the classical prime mass input.
No increment-provider hypothesis remains in this theorem. -/
theorem quantitative_recurrence_of_source_witnesses {ℓ : ℕ}
    (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput) (P : PolynomialFamily ℓ)
    (d Bmax Aq Aε T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hmax : ∀ i, (P.polynomials i).natDegree ≤ d)
    (htop : ∃ i, (P.polynomials i).natDegree = d)
    (C : ℝ) (hC : 1 ≤ C) (hcoeff : ∀ i j, (|(P.polynomials i).coeff j| : ℝ) ≤ C)
    (reg : KMTTRegularityWitness C d ℓ Bmax Aq Aε T)
    (p : KMTTComparisonParameters ℓ reg.Adiv)
    (hUW : KMTTUnweightedWitness C d ℓ reg.Adiv p)
    (mass : PrimeProgressionMassWitness p d (1 / (10 * C * (d + 1 : ℕ)))) :
    QuantitativeRecurrence P := by
  classical
  obtain ⟨cstar, hcstar, hdiscrepancy⟩ := ps_prime_discrepancy hSS hVN d hd
  obtain ⟨c₂, hc₂, Ninc, hIncrement⟩ :=
    kmtt_density_increment_of_witnesses C d ℓ Bmax Aq Aε T hd hT reg p hUW
  let cLength : ℝ := reg.resolutionConstant * (p.c₁ / 16) ^ Aε
  have hcLength : 0 < cLength := mul_pos reg.resolutionConstant_pos
    (pow_pos (div_pos p.c₁_pos (by norm_num)) _)
  have hrd : firstDegree P ≤ d := hmax _
  obtain ⟨κ, hκ, hconstruction⟩ := quantitative_recurrence_from_steps P d Bmax Aq
    (3 * (ℓ + 1) * Aε) hd hrd p c₂ cLength hc₂ hcLength
  refine ⟨cstar, hcstar, κ, hκ, ?_⟩
  intro c hc hcc
  have hcoeff' : ∀ i j, j ≤ d → |((P.polynomials i).coeff j : ℝ)| ≤ C := by
    intro i j _
    exact_mod_cast hcoeff i j
  obtain ⟨Ndisc, hdisc⟩ := hdiscrepancy ℓ P hmax htop C hC hcoeff' reg.Adiv p mass c hc hcc
  have hprovider : ∀ s : ℕ, ∀ S : RecurrenceState P c s, max Ninc Ndisc ≤ S.size →
      KMTTAdmissible p S.size S.modulus s S.density →
      ∃ S' : RecurrenceState P c s,
        Nonempty (RecurrenceStep d Bmax Aq (3 * (ℓ + 1) * Aε) c₂ cLength S S') := by
    intro s S hN hadm
    have hQ : 0 < S.modulus := by have := S.modulus_pos; omega
    let R := P.rescaled S.modulus hQ
    have hCQ : ∀ i, HasCQCoefficients C S.modulus (R.polynomials i) := by
      intro i
      exact rescale_hasCQCoefficients (P.polynomials i) S.modulus S.modulus_pos
        (P.zero_constant i) (P.positive_degree i) C hC (hcoeff i)
    have hmaxR : ∀ i, (R.polynomials i).natDegree ≤ d := by
      intro i
      simpa only [R, PolynomialFamily.natDegree_rescaled] using hmax i
    have htopR : ∃ i, (R.polynomials i).natDegree = d := by
      obtain ⟨i, hi⟩ := htop
      exact ⟨i, by simpa only [R, PolynomialFamily.natDegree_rescaled] using hi⟩
    have hdensity := S.density_identity
    have hweighted := hdisc S.size ((le_max_right _ _).trans hN) S.modulus s S.density
      hadm S.set S.subset hdensity S.forbidden
    have hinc := hIncrement S.size ((le_max_left _ _).trans hN) S.modulus s S.density
      hadm R hCQ hmaxR htopR S.set S.subset hdensity hweighted
    exact recurrenceState_next_of_increment P c s d Bmax Aq (3 * (ℓ + 1) * Aε)
      c₂ cLength S hinc
  have hsets := hconstruction c (max Ninc Ndisc) hprovider
  obtain ⟨Nsets, hsets'⟩ := Filter.eventually_atTop.mp hsets
  refine ⟨max Nsets 3, ?_⟩
  intro N hN A hA hbound
  have hNsets : Nsets ≤ N := (le_max_left _ _).trans hN
  have hN₃ : 3 ≤ N := (le_max_right _ _).trans hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hdense : (Real.log (N : ℝ)) ^ (-κ) ≤ setDensity N A := by
    rw [Real.rpow_neg hlog]
    apply (le_div_iff₀ hNreal).mpr
    simpa only [div_eq_mul_inv, mul_comm] using hbound
  exact hsets' N hNsets A hA hdense

/-- Theorem 1.1 for the authoritative manuscript's actual integer polynomial
family and actual Piatetski--Shapiro primes, conditional on four transparent
external input families. In particular the two KMTT witnesses are selected
jointly and no original conclusion is assumed. -/
theorem quantitative_recurrence
    (hSS : ShaoSunPhaseInput) (hVN : FiniteVNInput)
    (hReg : KMTTRegularityInput) (hJoint : KMTTCompatibleInput)
    {ℓ : ℕ} (P : PolynomialFamily ℓ) : QuantitativeRecurrence P := by
  classical
  let last : Fin ℓ := ⟨ℓ - 1, by have := P.nonempty; omega⟩
  let d : ℕ := (P.polynomials last).natDegree
  have hd : 1 ≤ d := P.positive_degree last
  have hmax : ∀ i, (P.polynomials i).natDegree ≤ d := by
    intro i
    exact P.increasing_degrees.monotone (Fin.le_iff_val_le_val.mpr
      (by have := i.isLt; dsimp [last]; omega))
  have htop : ∃ i, (P.polynomials i).natDegree = d := ⟨last, rfl⟩
  let C : ℝ := familyCoefficientBound P.polynomials
  have hC : 1 ≤ C := one_le_familyCoefficientBound P.polynomials
  have hcoeff : ∀ i j, (|(P.polynomials i).coeff j| : ℝ) ≤ C :=
    coefficient_le_familyCoefficientBound P.polynomials
  obtain ⟨Bmax, _, hRegd⟩ := hReg d hd
  obtain ⟨Aq, Aε, T, _, _, hT, hRegℓ⟩ := hRegd ℓ (by have := P.nonempty; omega)
  obtain ⟨reg⟩ := hRegℓ C hC
  let τmax : ℝ := 1 / (10 * C * (d + 1 : ℕ))
  have hτmax : 0 < τmax := by
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    dsimp [τmax]
    positivity
  obtain ⟨p, hUW, ⟨mass⟩⟩ := hJoint C hC d ℓ hd (by have := P.nonempty; omega)
    reg.Adiv τmax hτmax
  exact quantitative_recurrence_of_source_witnesses hSS hVN P d Bmax Aq Aε T hd hT
    hmax htop C hC hcoeff reg p hUW mass

end PSPrimes
