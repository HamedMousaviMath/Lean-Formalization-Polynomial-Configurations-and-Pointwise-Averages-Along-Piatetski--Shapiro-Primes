import PSPrimes.KMTTInterfaces
import PSPrimes.AsymptoticScales
import PSPrimes.SmallScale

noncomputable section
open scoped BigOperators
namespace PSPrimes

@[simp] theorem card_initialInterval (M : ℕ) : (initialInterval M).card = M := by
  simp [initialInterval]

/-- Exact real/complex and endpoint bridge to the checked local-density form. -/
theorem realConfigurationForm_sub_model {ℓ : ℕ} (N M Q : ℕ)
    (P : Fin ℓ → Polynomial ℤ) (F : Fin (ℓ + 1) → ℤ → ℝ) (δ : ℝ) :
    ((realConfigurationForm N M Q P (fun _ => 1) F -
      realModelCount N M Q P (fun _ => 1) δ : ℝ) : ℂ) =
      (((integerInterval N).card : ℂ) * ((initialInterval M).card : ℂ))⁻¹ *
        localFactorDifference Finset.univ (integerInterval N) (integerInterval N)
          (initialInterval M) (fun i y => (recurrencePolynomials P i).eval (y : ℤ)) F δ := by
  simp only [realConfigurationForm, realModelCount, realIndicator, localFactorDifference,
    card_integerInterval, card_initialInterval, one_mul, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum,
    Complex.ofReal_prod, Finset.sum_sub_distrib, mul_sub]
  simp only [apply_ite, Complex.ofReal_zero]

/-- A model comparison after regularity approximation retains the unweighted
set/model discrepancy up to exactly the quoted approximation error. -/
theorem regularity_retains_discrepancy {set model approximant ε D : ℝ}
    (hset : D ≤ |set - model|) (happrox : |set - approximant| ≤ ε) :
    D - ε ≤ |approximant - model| := by
  have htri : |set - model| ≤ |set - approximant| + |approximant - model| := by
    calc
      |set - model| = |(set - approximant) + (approximant - model)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

/-- Exact extraction of a dense progression once the primitive KMTT regularity
output and a strict local discrepancy are available. The approximation,
source small-scale alternative and admissibility are not assumed conclusions
of this theorem; they are separate steps of the source application. -/
theorem dense_progression_of_local_discrepancy {ℓ : ℕ}
    (N M Q b : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (hQ : 1 ≤ Q)
    (R : PolynomialFamily ℓ) (A : Finset ℤ) (hA : A ⊆ integerInterval N)
    (δ c₂ : ℝ) (hδ : 0 ≤ δ) (hc₂ : 0 ≤ c₂)
    (hdensity : (A.card : ℝ) = δ * N)
    (factors : Fin (ℓ + 1) → ArithmeticLocalFactor N (Q ^ b))
    (F : Fin (ℓ + 1) → ℤ → ℝ)
    (hproj : ∀ i, IsLocalProjection (factors i) (realIndicator A 1) (F i))
    (hdisc : 2 * (ℓ + 1 : ℝ) * c₂ * (1 + c₂) ^ ℓ * δ ^ (ℓ + 1) <
      |realConfigurationForm N M Q R.polynomials (fun _ => 1) F -
        realModelCount N M Q R.polynomials (fun _ => 1) δ|) :
    ∃ i : Fin (ℓ + 1), ∃ a : ℤ, ∃ L : ℕ,
      1 ≤ L ∧ arithmeticProgression a (Q ^ b) L ⊆ integerInterval N ∧
      (1 + c₂) * δ * L < ((A ∩ arithmeticProgression a (Q ^ b) L).card : ℝ) ∧
      (factors i).resolution ≤ L := by
  classical
  have hU : (integerInterval N).Nonempty := integerInterval_nonempty hN
  have hJ : (initialInterval M).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
  have hcomplex : ‖(((integerInterval N).card : ℂ) * ((initialInterval M).card : ℂ))⁻¹ *
      localFactorDifference Finset.univ (integerInterval N) (integerInterval N)
        (initialInterval M) (fun i y => (recurrencePolynomials R.polynomials i).eval (y : ℤ)) F δ‖ =
      |realConfigurationForm N M Q R.polynomials (fun _ => 1) F -
        realModelCount N M Q R.polynomials (fun _ => 1) δ| := by
    rw [← realConfigurationForm_sub_model]
    exact Complex.norm_real _
  have hdisc' : 2 * ((Finset.univ : Finset (Fin (ℓ + 1))).card : ℝ) * c₂ *
      (1 + c₂) ^ ((Finset.univ : Finset (Fin (ℓ + 1))).card - 1) *
      δ ^ (Finset.univ : Finset (Fin (ℓ + 1))).card <
      ‖(((integerInterval N).card : ℂ) * ((initialInterval M).card : ℂ))⁻¹ *
        localFactorDifference Finset.univ (integerInterval N) (integerInterval N)
          (initialInterval M) (fun i y => (recurrencePolynomials R.polynomials i).eval (y : ℤ)) F δ‖ := by
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, hcomplex,
      Nat.cast_add, Nat.cast_one] using hdisc
  obtain ⟨i, _, B, hB, hinc⟩ := density_increment_from_local_discrepancy
    (Finset.univ : Finset (Fin (ℓ + 1))) A (integerInterval N) (integerInterval N)
    (initialInterval M) (fun i y => (recurrencePolynomials R.polynomials i).eval (y : ℤ))
    (fun i => (factors i).cells) F Finset.univ_nonempty hU hJ hA hδ hc₂
    (by simpa only [card_integerInterval, mul_comm] using hdensity)
    (fun i _ => (factors i).cover) (fun i _ => (factors i).disjoint)
    (fun i _ => (factors i).atoms_nonempty)
    (fun i _ atom ha x hx => by rw [(hproj i).2 atom ha x hx, cellMean_indicator])
    (fun i _ => (hproj i).1) hdisc'
  obtain ⟨a, L, hBL, hL, _⟩ := (factors i).atoms_progressions B hB
  have hLpos : 1 ≤ L := (factors i).resolution_pos.trans hL
  refine ⟨i, a, L, hLpos, ?_, ?_, hL⟩
  · rw [← hBL]
    exact (factors i).atom_subset hB
  · have hQpow : 0 < Q ^ b := pow_pos (by omega) _
    simpa only [hBL, card_arithmeticProgression a (Q ^ b) L hQpow, mul_assoc] using hinc

/-- The regularity error chosen in the manuscript. -/
def regularityError {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv) (δ : ℝ) : ℝ :=
  (p.c₁ / 16) * δ ^ (3 * (ℓ + 1))

theorem regularityError_pos {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    {δ : ℝ} (hδ : 0 < δ) : 0 < regularityError p δ := by
  unfold regularityError
  exact mul_pos (by linarith [p.c₁_pos]) (pow_pos hδ _)

theorem regularityError_le {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    regularityError p δ ≤ p.c₁ * δ ^ (ℓ + 1) / 16 := by
  unfold regularityError
  have hp : δ ^ (3 * (ℓ + 1)) ≤ δ ^ (ℓ + 1) :=
    pow_le_pow_of_le_one hδ hδ₁ (by omega)
  nlinarith [mul_le_mul_of_nonneg_left hp p.c₁_pos.le]

theorem regularityError_lt_half {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) : regularityError p δ < 1 / 2 := by
  have hp : δ ^ (ℓ + 1) ≤ 1 := pow_le_one₀ hδ hδ₁
  have hc := mul_le_mul_of_nonneg_left hp p.c₁_pos.le
  have he := regularityError_le p hδ hδ₁
  nlinarith [p.c₁_le]

/-- Source (5.36) is proved from the numerical compatibility conditions,
rather than bundled into an external theorem's conclusion. -/
theorem regularity_cutoff_le {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ⌈(regularityError p δ) ^ (-(Adiv : ℝ))⌉₊ ≤ ⌈p.K₁ * δ ^ (-p.C₁)⌉₊ := by
  have heps := regularityError_pos p hδ
  have hid : (regularityError p δ) ^ (-(Adiv : ℝ)) =
      (16 / p.c₁) ^ Adiv * δ ^ (-((3 * (ℓ + 1) * Adiv : ℕ) : ℝ)) := by
    rw [Real.rpow_neg heps.le, Real.rpow_natCast,
      Real.rpow_neg hδ.le, Real.rpow_natCast]
    unfold regularityError
    rw [mul_pow, ← pow_mul, mul_inv_rev, ← inv_pow]
    simp only [← inv_pow, inv_div, div_one]
    ring
  apply Nat.ceil_mono
  rw [hid]
  have hc : (16 / p.c₁) ^ Adiv ≤ p.K₁ := by
    linarith [p.divisibility_constant]
  have hpow : δ ^ (-((3 * (ℓ + 1) * Adiv : ℕ) : ℝ)) ≤ δ ^ (-p.C₁) := by
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ₁
    have := p.divisibility_exponent
    push_cast
    push_cast at this
    linarith
  exact mul_le_mul hc hpow (Real.rpow_nonneg hδ.le _) (by linarith [p.K₁_ge])

/-- The actual divisibility required by weak regularity follows from the
fixed smoothness parameter's lcm divisibility. -/
theorem regularity_divisibility {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {Q s : ℕ}
    (hcut : ⌈p.K₁ * δ ^ (-p.C₁)⌉₊ ≤ s) (hdiv : smoothModulus s ∣ Q) :
    smoothModulus ⌈(regularityError p δ) ^ (-(Adiv : ℝ))⌉₊ ∣ Q := by
  apply dvd_trans (b := smoothModulus s) _ hdiv
  apply Finset.lcm_dvd
  intro k hk
  obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
  exact dvd_smoothModulus hk₁ (hk₂.trans ((regularity_cutoff_le p hδ hδ₁).trans hcut))

/-- A fixed positive increment parameter with the strict telescoping margin. -/
theorem exists_increment_parameter (k : ℕ) (hk : 1 ≤ k) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₁ : c₁ ≤ 1) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ c₂ ≤ 1 ∧
      2 * (k : ℝ) * c₂ * (1 + c₂) ^ (k - 1) < c₁ / 8 := by
  let den : ℝ := 32 * k * (2 : ℝ) ^ (k - 1)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
  have hden : 0 < den := by dsimp [den]; positivity
  have hden₁ : 1 ≤ den := by dsimp [den]; nlinarith
  let c₂ : ℝ := c₁ / den
  have hc₂ : 0 < c₂ := div_pos hc₁ hden
  have hc₂₁ : c₂ ≤ 1 := (div_le_one hden).mpr (hc₁₁.trans hden₁)
  refine ⟨c₂, hc₂, hc₂₁, ?_⟩
  have hpp : (1 + c₂) ^ (k - 1) ≤ (2 : ℝ) ^ (k - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  calc
    2 * (k : ℝ) * c₂ * (1 + c₂) ^ (k - 1) ≤
        2 * (k : ℝ) * c₂ * (2 : ℝ) ^ (k - 1) :=
      mul_le_mul_of_nonneg_left hpp (by positivity)
    _ = c₁ / 16 := by
      dsimp [c₂, den]
      field_simp
      ring
    _ < c₁ / 8 := by linarith

/-- The precise loss when the shorter shift scale is raised to a degree.
The square-root exponential uses the largest degree, as in (23). -/
theorem truncated_scale_power_lower (M M₀ r d : ℕ) (hrd : r ≤ d)
    (htrunc : (M : ℝ) * Real.exp (-Real.sqrt (Real.log (M : ℝ))) ≤ M₀) :
    (M : ℝ) ^ r * Real.exp (-(d : ℝ) * Real.sqrt (Real.log (M : ℝ))) ≤ (M₀ : ℝ) ^ r := by
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  calc
    (M : ℝ) ^ r * Real.exp (-(d : ℝ) * Real.sqrt (Real.log (M : ℝ))) ≤
        (M : ℝ) ^ r * Real.exp (-(r : ℝ) * Real.sqrt (Real.log (M : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg M) _)
      apply Real.exp_le_exp.mpr
      nlinarith [Real.sqrt_nonneg (Real.log (M : ℝ))]
    _ = ((M : ℝ) * Real.exp (-Real.sqrt (Real.log (M : ℝ)))) ^ r := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      ring_nf
    _ ≤ (M₀ : ℝ) ^ r := pow_le_pow_left₀ (by positivity) htrunc _

/-- Resolution at coordinate i dominates the minimum-degree scale, with
all prefactors and δ exponents retained explicitly. -/
theorem regularity_resolution_lower {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    (R : PolynomialFamily ℓ) (M M₀ Q d Aq Aε : ℕ) (hM₀ : 1 ≤ M₀)
    {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (hc : 0 ≤ c)
    (hdeg : firstDegree R ≤ d)
    (htrunc : (M : ℝ) * Real.exp (-Real.sqrt (Real.log (M : ℝ))) ≤ M₀)
    (i : Fin (ℓ + 1)) :
    (c * (p.c₁ / 16) ^ Aε) * (Q : ℝ) ^ (-(Aq : ℝ)) *
        δ ^ (3 * (ℓ + 1) * Aε) * (M : ℝ) ^ firstDegree R *
        Real.exp (-(d : ℝ) * Real.sqrt (Real.log (M : ℝ))) ≤
      c * (Q : ℝ) ^ (-(Aq : ℝ)) * (regularityError p δ) ^ Aε *
        (M₀ : ℝ) ^ coordinateDegrees R i := by
  have hM₀R : (1 : ℝ) ≤ M₀ := by exact_mod_cast hM₀
  have hpow : (M : ℝ) ^ firstDegree R *
      Real.exp (-(d : ℝ) * Real.sqrt (Real.log (M : ℝ))) ≤
      (M₀ : ℝ) ^ coordinateDegrees R i :=
    (truncated_scale_power_lower M M₀ (firstDegree R) d hdeg htrunc).trans
      (pow_le_pow_right₀ hM₀R (firstDegree_le_coordinate R i))
  have hεpow : (regularityError p δ) ^ Aε =
      (p.c₁ / 16) ^ Aε * δ ^ (3 * (ℓ + 1) * Aε) := by
    rw [regularityError, mul_pow, ← pow_mul]
  have hcoeff : 0 ≤ c * (Q : ℝ) ^ (-(Aq : ℝ)) * (regularityError p δ) ^ Aε := by
    exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg Q) _))
      (pow_nonneg (regularityError_pos p hδ).le _)
  calc
    _ = (c * (Q : ℝ) ^ (-(Aq : ℝ)) * (regularityError p δ) ^ Aε) *
        ((M : ℝ) ^ firstDegree R * Real.exp (-(d : ℝ) * Real.sqrt (Real.log (M : ℝ)))) := by
      rw [hεpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hcoeff

/-- The output of manuscript Proposition 3.1 with its O-notation unpacked.
`Bmax` bounds b; `Aq,Aδ` are explicit exponents and `cLength` is the positive
prefactor implicit in the original length estimate. -/
def DensityIncrementResult {ℓ : ℕ} (R : PolynomialFamily ℓ) (A : Finset ℤ)
    (N Q d Bmax Aq Aδ : ℕ) (δ c₂ cLength : ℝ) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ b ≤ Bmax ∧ ∃ a : ℤ, ∃ N' : ℕ,
    1 ≤ N' ∧ arithmeticProgression a (Q ^ b) N' ⊆ integerInterval N ∧
    (1 + c₂) * δ * N' ≤ ((A ∩ arithmeticProgression a (Q ^ b) N').card : ℝ) ∧
    cLength * (Q : ℝ) ^ (-(Aq : ℝ)) * δ ^ Aδ *
      (floorScale N Q d : ℝ) ^ firstDegree R *
      Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale N Q d : ℝ))) ≤ N'

/-- Finite application of the primitive regularity alternative. No denser
progression is assumed: the source yields partitions, and the checked local
argument extracts the dense atom and proves its actual length lower bound. -/
theorem densityIncrement_of_unweighted_discrepancy {ℓ Adiv : ℕ}
    (C : ℝ) (d Bmax Aq Aε T : ℕ) (p : KMTTComparisonParameters ℓ Adiv)
    (reg : KMTTRegularityWitness C d ℓ Bmax Aq Aε T) (hAdiv : reg.Adiv = Adiv)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hmargin : 2 * (ℓ + 1 : ℝ) * c₂ * (1 + c₂) ^ ℓ < p.c₁ / 8)
    (N Q s M₀ : ℕ) (δ : ℝ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hcut : ⌈p.K₁ * δ ^ (-p.C₁)⌉₊ ≤ s) (hdiv : smoothModulus s ∣ Q)
    (hM₀ : 1 ≤ M₀) (hM₀root : (M₀ : ℝ) ≤ rootScale N Q d)
    (htrunc : (floorScale N Q d : ℝ) *
      Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ))) ≤ M₀)
    (hlarge : reg.smallConstant * ((Q : ℝ) / regularityError p δ) ^ T < M₀)
    (R : PolynomialFamily ℓ) (hCQ : ∀ i, HasCQCoefficients C Q (R.polynomials i))
    (hmax : ∀ i, (R.polynomials i).natDegree ≤ d)
    (htop : ∃ i, (R.polynomials i).natDegree = d)
    (A : Finset ℤ) (hA : A ⊆ integerInterval N) (hdensity : (A.card : ℝ) = δ * N)
    (hdisc : p.c₁ * δ ^ (ℓ + 1) / 4 ≤
      |realSetCount N M₀ Q R.polynomials (fun _ => 1) A -
        realModelCount N M₀ Q R.polynomials (fun _ => 1) δ|) :
    DensityIncrementResult R A N Q d Bmax Aq (3 * (ℓ + 1) * Aε) δ c₂
      (reg.resolutionConstant * (p.c₁ / 16) ^ Aε) := by
  classical
  let ε := regularityError p δ
  have hε : 0 < ε := regularityError_pos p hδ
  have hεhalf : ε < 1 / 2 := regularityError_lt_half p hδ.le hδ₁
  have hεdiv : smoothModulus ⌈ε ^ (-(reg.Adiv : ℝ))⌉₊ ∣ Q := by
    rw [hAdiv]
    exact regularity_divisibility p hδ hδ₁ hcut hdiv
  have hunit (i : Fin (ℓ + 1)) (x : ℤ) : |realIndicator A 1 x| ≤ 1 := by
    unfold realIndicator
    split_ifs <;> norm_num
  have hsupp (i : Fin (ℓ + 1)) (x : ℤ) (hx : x ∉ integerInterval N) : realIndicator A 1 x = 0 := by
    have hxA : x ∉ A := fun ha => hx (hA ha)
    simp [realIndicator, hxA]
  obtain hsmall | ⟨b, hb, hbmax, factors, F, hproj, hres, happ⟩ :=
    reg.regularity N Q M₀ hN hQ hM₀ hM₀root ε hε hεhalf hεdiv R hCQ hmax htop
      (fun _ => realIndicator A 1) hunit hsupp
  · exact False.elim ((not_le_of_gt hlarge) hsmall)
  · have hretain := regularity_retains_discrepancy hdisc happ
    have hεsmall : ε ≤ p.c₁ * δ ^ (ℓ + 1) / 16 := regularityError_le p hδ.le hδ₁
    have hpow : 0 < δ ^ (ℓ + 1) := pow_pos hδ _
    have hmargin' := mul_lt_mul_of_pos_right hmargin hpow
    have hlocal : 2 * (ℓ + 1 : ℝ) * c₂ * (1 + c₂) ^ ℓ * δ ^ (ℓ + 1) <
        |realConfigurationForm N M₀ Q R.polynomials (fun _ => 1) F -
          realModelCount N M₀ Q R.polynomials (fun _ => 1) δ| := by
      change p.c₁ * δ ^ (ℓ + 1) / 4 - ε ≤ _ at hretain
      nlinarith [mul_pos p.c₁_pos hpow]
    obtain ⟨i, a, L, hL, hsub, hinc, hLres⟩ := dense_progression_of_local_discrepancy
      N M₀ Q b hN hM₀ hQ R A hA δ c₂ hδ.le hc₂.le hdensity factors F hproj hlocal
    refine ⟨b, hb, hbmax, a, L, hL, hsub, hinc.le, ?_⟩
    have hr := regularity_resolution_lower p R (floorScale N Q d) M₀ Q d Aq Aε hM₀
      hδ reg.resolutionConstant reg.resolutionConstant_pos.le (hmax _) htrunc i
    exact (hr.trans (hres i)).trans (by exact_mod_cast hLres)

/-- Full manuscript Proposition 3.1 for fixed compatible primitive inputs.
All admissibility and small-scale exclusions are proved for sufficiently
large N, uniformly in the density, modulus, smoothness cutoff, family and set.
The additional hypotheses are exactly the separately quoted KMTT source
comparison and weak regularity results, not an increment oracle. -/
theorem kmtt_density_increment_of_witnesses
    (C : ℝ) (d ℓ Bmax Aq Aε T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (reg : KMTTRegularityWitness C d ℓ Bmax Aq Aε T)
    (p : KMTTComparisonParameters ℓ reg.Adiv)
    (hUW : KMTTUnweightedWitness C d ℓ reg.Adiv p) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Nmin : ℕ,
      ∀ N : ℕ, Nmin ≤ N → ∀ Q s : ℕ, ∀ δ : ℝ,
        KMTTAdmissible p N Q s δ →
        ∀ R : PolynomialFamily ℓ,
          (∀ i, HasCQCoefficients C Q (R.polynomials i)) →
          (∀ i, (R.polynomials i).natDegree ≤ d) →
          (∃ i, (R.polynomials i).natDegree = d) →
          ∀ A : Finset ℤ, A ⊆ integerInterval N → (A.card : ℝ) = δ * N →
          p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) ≤
            |realSetCount N (floorScale N Q d) Q R.polynomials ArithmeticFunction.vonMangoldt A -
              realModelCount N (floorScale N Q d) Q R.polynomials ArithmeticFunction.vonMangoldt δ| →
          DensityIncrementResult R A N Q d Bmax Aq (3 * (ℓ + 1) * Aε) δ c₂
            (reg.resolutionConstant * (p.c₁ / 16) ^ Aε) := by
  obtain ⟨c₂, hc₂, _, hmargin⟩ := exists_increment_parameter (ℓ + 1) (by omega) p.c₁_pos p.c₁_le
  have hmargin' : 2 * (ℓ + 1 : ℝ) * c₂ * (1 + c₂) ^ ℓ < p.c₁ / 8 := by
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using hmargin
  have ha : 2 * p.c₀ < 1 := by linarith [p.c₀_lt]
  have hCb : 0 < (1 / p.C₁ ^ 2 : ℝ) := by
    have := p.C₁_ge
    positivity
  have he₀ : 0 < p.c₁ / 16 := by linarith [p.c₁_pos]
  have hsmall := eventually_not_small_scale_alternative ha hCb he₀ reg.smallConstant_pos
    d (3 * (ℓ + 1)) T hd (by omega) hT
  have hfloor := eventually_floorScale_pos ha d (by omega)
  have hgood : ∀ᶠ N : ℕ in Filter.atTop,
      (3 ≤ N) ∧
      (∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ Real.exp ((Real.log N) ^ (2 * p.c₀)) →
        1 ≤ floorScale N Q d) ∧
      (∀ Q : ℕ, 1 ≤ Q → ∀ δ : ℝ,
        (Real.log N) ^ (-(1 / p.C₁ ^ 2)) < δ →
        (Q : ℝ) ≤ Real.exp ((Real.log N) ^ (2 * p.c₀)) → ∀ M₀ : ℕ,
        ⌈(floorScale N Q d : ℝ) *
          Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ)))⌉₊ ≤ M₀ →
        ¬((M₀ : ℝ) ≤ reg.smallConstant * ((Q : ℝ) / regularityError p δ) ^ T)) := by
    filter_upwards [Filter.eventually_ge_atTop 3, hfloor, hsmall] with N hN hf hs
    exact ⟨hN, hf, hs⟩
  obtain ⟨Naux, haux⟩ := Filter.eventually_atTop.mp hgood
  obtain ⟨Nsource, hsource⟩ := hUW
  refine ⟨c₂, hc₂, max Naux Nsource, ?_⟩
  intro N hN Q s δ hadm R hCQ hmax htop A hA hdensity hdisc
  have hNaux : Naux ≤ N := (le_max_left _ _).trans hN
  have hNsource : Nsource ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hN₃, hMpos, hnotSmall⟩ := haux N hNaux
  obtain ⟨hQ, hs, hδlower, hδ₁, hcut, hsupper, hQupper, hQsmooth, hQdiv⟩ := hadm
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hδ : 0 < δ :=
    (Real.rpow_pos_of_pos (Real.log_pos hNr) _).trans hδlower
  obtain ⟨M₀, htruncNat, hM₀M, hdisc₀⟩ := hsource N hNsource Q s δ
    ⟨hQ, hs, hδlower, hδ₁, hcut, hsupper, hQupper, hQsmooth, hQdiv⟩ R hCQ hmax htop A hA hdensity hdisc
  have hM : 1 ≤ floorScale N Q d := hMpos Q hQ hQupper
  have htrunc : (floorScale N Q d : ℝ) *
      Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ))) ≤ M₀ :=
    (Nat.le_ceil _).trans (by exact_mod_cast htruncNat)
  have hM₀ : 1 ≤ M₀ := by
    have hpos : (0 : ℝ) < (M₀ : ℝ) :=
      (mul_pos (by exact_mod_cast (by omega : 0 < floorScale N Q d)) (Real.exp_pos _)).trans_le htrunc
    have hposNat : 0 < M₀ := by exact_mod_cast hpos
    omega
  have hM₀root : (M₀ : ℝ) ≤ rootScale N Q d :=
    (by exact_mod_cast hM₀M : (M₀ : ℝ) ≤ (floorScale N Q d : ℝ)).trans (floorScale_le_root N Q d)
  have hlarge : reg.smallConstant * ((Q : ℝ) / regularityError p δ) ^ T < M₀ :=
    lt_of_not_ge (hnotSmall Q hQ δ hδlower hQupper M₀ htruncNat)
  exact densityIncrement_of_unweighted_discrepancy C d Bmax Aq Aε T p reg rfl
    c₂ hc₂ hmargin' N Q s M₀ δ (by omega) hQ hδ hδ₁ hcut hQdiv hM₀ hM₀root
    htrunc hlarge R hCQ hmax htop A hA hdensity hdisc₀

/-- The complete conclusion of Proposition 3.1 for a fixed compatible choice
of constants. In particular it has no extra small-scale or divisibility
premise beyond the manuscript's displayed admissibility conditions. -/
def KMTTDensityIncrementWitness (C : ℝ) (d ℓ Adiv Bmax Aq Aδ : ℕ)
    (p : KMTTComparisonParameters ℓ Adiv) (c₂ cLength : ℝ) : Prop :=
  ∃ Nmin : ℕ, ∀ N : ℕ, Nmin ≤ N → ∀ Q s : ℕ, ∀ δ : ℝ,
    KMTTAdmissible p N Q s δ →
    ∀ R : PolynomialFamily ℓ,
      (∀ i, HasCQCoefficients C Q (R.polynomials i)) →
      (∀ i, (R.polynomials i).natDegree ≤ d) →
      (∃ i, (R.polynomials i).natDegree = d) →
      ∀ A : Finset ℤ, A ⊆ integerInterval N → (A.card : ℝ) = δ * N →
      p.c₁ * δ ^ (ℓ + 1) * primeProgressionMass Q (floorScale N Q d) ≤
        |realSetCount N (floorScale N Q d) Q R.polynomials ArithmeticFunction.vonMangoldt A -
          realModelCount N (floorScale N Q d) Q R.polynomials ArithmeticFunction.vonMangoldt δ| →
      DensityIncrementResult R A N Q d Bmax Aq Aδ δ c₂ cLength

/-- Manuscript Proposition 3.1, conditional on the separately quoted source
Proposition 5.2 and Lemma 5.3. The order of the constants makes the common
modulus exponent depend only on d, and the q/δ length exponents only on d,ℓ.
All remaining original local, length, divisibility and large-N arguments are
proved by this module and its checked elementary dependencies. -/
theorem kmtt_density_increment (hUW : KMTTUnweightedInput) (hReg : KMTTRegularityInput) :
    ∀ d : ℕ, 1 ≤ d → ∃ Bmax : ℕ, 1 ≤ Bmax ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ Aq Aδ : ℕ, 1 ≤ Aq ∧ 1 ≤ Aδ ∧
        ∀ C : ℝ, 1 ≤ C → ∃ Adiv : ℕ,
          ∃ p : KMTTComparisonParameters ℓ Adiv,
          ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ cLength : ℝ, 0 < cLength ∧
            KMTTDensityIncrementWitness C d ℓ Adiv Bmax Aq Aδ p c₂ cLength := by
  intro d hd
  obtain ⟨Bmax, hBmax, hRegd⟩ := hReg d hd
  refine ⟨Bmax, hBmax, ?_⟩
  intro ℓ hℓ
  obtain ⟨Aq, Aε, T, hAq, hAε, hT, hRegℓ⟩ := hRegd ℓ hℓ
  have hAδ : 1 ≤ 3 * (ℓ + 1) * Aε := by
    have hpos : 0 < 3 * (ℓ + 1) * Aε := by positivity
    omega
  refine ⟨Aq, 3 * (ℓ + 1) * Aε, hAq, hAδ, ?_⟩
  intro C hC
  obtain ⟨reg⟩ := hRegℓ C hC
  obtain ⟨p, hUWp⟩ := hUW C hC d ℓ hd hℓ reg.Adiv
  obtain ⟨c₂, hc₂, hw⟩ := kmtt_density_increment_of_witnesses
    C d ℓ Bmax Aq Aε T hd hT reg p hUWp
  refine ⟨reg.Adiv, p, c₂, hc₂, reg.resolutionConstant * (p.c₁ / 16) ^ Aε, ?_, hw⟩
  exact mul_pos reg.resolutionConstant_pos (pow_pos (by linarith [p.c₁_pos]) _)

end PSPrimes
