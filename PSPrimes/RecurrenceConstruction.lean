import PSPrimes.ConfigurationTransport
import PSPrimes.RecurrenceAlgebra
import PSPrimes.DensityIncrement
import PSPrimes.FiniteIterationBounds
import PSPrimes.LogScales
import PSPrimes.InitialProgression

noncomputable section
namespace PSPrimes

/-- An actual stage of the set iteration, retaining the exact forbidden
PS-prime configuration and the fixed smoothness parameter. -/
structure RecurrenceState {ℓ : ℕ} (P : PolynomialFamily ℓ) (c : ℝ) (s : ℕ) where
  size : ℕ
  modulus : ℕ
  set : Finset ℤ
  size_pos : 1 ≤ size
  modulus_pos : 1 ≤ modulus
  subset : set ⊆ integerInterval size
  smooth : SmoothUpTo s modulus
  saturated : smoothModulus s ∣ modulus
  forbidden : NoRescaledConfiguration P.polynomials modulus c set

namespace RecurrenceState

def density {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (S : RecurrenceState P c s) : ℝ := setDensity S.size S.set

theorem density_nonneg {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (S : RecurrenceState P c s) : 0 ≤ S.density := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem density_le_one {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (S : RecurrenceState P c s) : S.density ≤ 1 := by
  have hc := Finset.card_le_card S.subset
  rw [card_integerInterval] at hc
  have hsz : (0 : ℝ) < S.size := by exact_mod_cast (by have := S.size_pos; omega : 0 < S.size)
  exact (div_le_one hsz).mpr (by exact_mod_cast hc)

theorem density_identity {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (S : RecurrenceState P c s) : (S.set.card : ℝ) = S.density * S.size := by
  have hsz : (S.size : ℝ) ≠ 0 := by exact_mod_cast (by have := S.size_pos; omega : S.size ≠ 0)
  exact (div_mul_cancel₀ _ hsz).symm

end RecurrenceState

/-- The actual affine progression update, together with the quantitative
inequalities used by the finite logarithmic bookkeeping. -/
structure RecurrenceStep {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (d Bmax Aq Aδ : ℕ) (c₂ cLength : ℝ) (S S' : RecurrenceState P c s) where
  exponent : ℕ
  exponent_pos : 1 ≤ exponent
  exponent_le : exponent ≤ Bmax
  origin : ℤ
  modulus_update : S'.modulus = S.modulus ^ (exponent + 1)
  set_update : S'.set = affinePullback S.set origin (S.modulus ^ exponent) S'.size
  size_nonincrease : S'.size ≤ S.size
  density_growth : (1 + c₂) * S.density ≤ S'.density
  length_lower : cLength * (S.modulus : ℝ) ^ (-(Aq : ℝ)) * S.density ^ Aδ *
    (floorScale S.size S.modulus d : ℝ) ^ firstDegree P *
    Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale S.size S.modulus d : ℝ))) ≤ S'.size

/-- A source increment constructs the next genuine set, including the exact
prime-parameter invariant. It is not an assumed transition relation. -/
theorem recurrenceState_next_of_increment {ℓ : ℕ} (P : PolynomialFamily ℓ)
    (c : ℝ) (s d Bmax Aq Aδ : ℕ) (c₂ cLength : ℝ) (S : RecurrenceState P c s)
    (hinc : DensityIncrementResult (P.rescaled S.modulus (by have := S.modulus_pos; omega))
      S.set S.size S.modulus d Bmax Aq Aδ S.density c₂ cLength) :
    ∃ S' : RecurrenceState P c s, Nonempty (RecurrenceStep d Bmax Aq Aδ c₂ cLength S S') := by
  obtain ⟨b, hb, hbmax, a, L, hL, hsub, hgrowth, hlength⟩ := hinc
  have hQ : 0 < S.modulus := by have := S.modulus_pos; omega
  have hQb : 0 < S.modulus ^ b := pow_pos hQ _
  let S' : RecurrenceState P c s := {
    size := L
    modulus := S.modulus ^ (b + 1)
    set := affinePullback S.set a (S.modulus ^ b) L
    size_pos := hL
    modulus_pos := by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hQ))
    subset := affinePullback_subset _ _ _ _
    smooth := S.smooth.pow _
    saturated := smoothModulus_dvd_pow S.saturated (by omega)
    forbidden := NoRescaledConfiguration.progression_pullback
      P.polynomials P.zero_constant S.modulus hQ b L c S.set a S.forbidden }
  refine ⟨S', ⟨b, hb, hbmax, a, rfl, rfl, ?_, ?_, ?_⟩⟩
  · have hcard := Finset.card_le_card hsub
    rw [card_arithmeticProgression a _ L hQb, card_integerInterval] at hcard
    exact hcard
  · exact density_affinePullback_ge S.set a (S.modulus ^ b) L hQb hL
      (1 + c₂) S.density hgrowth
  · change cLength * (S.modulus : ℝ) ^ (-(Aq : ℝ)) * S.density ^ Aδ *
      (floorScale S.size S.modulus d : ℝ) ^ firstDegree P *
      Real.exp (-(d : ℝ) * Real.sqrt (Real.log (floorScale S.size S.modulus d : ℝ))) ≤ L
    convert hlength using 1
    congr 3
    unfold firstDegree PolynomialFamily.rescaled
    exact (natDegree_rescale _ _ (by exact_mod_cast (Nat.ne_of_gt hQ))
      (by have := P.positive_degree ⟨0, P.nonempty⟩; omega)).symm

/-- Finite prefixes hold already constructed stages only. The values after
`n` are arbitrary and are never used as if future increments existed. -/
structure RecurrencePrefix {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (d Bmax Aq Aδ : ℕ) (c₂ cLength α Clog : ℝ) (initial : RecurrenceState P c s) (n : ℕ) where
  states : ℕ → RecurrenceState P c s
  zero : states 0 = initial
  steps : ∀ j < n, RecurrenceStep d Bmax Aq Aδ c₂ cLength (states j) (states (j + 1))
  log_steps : ∀ j < n, (firstDegree P : ℝ) / d * Real.log (states j).size -
    Clog * (Real.log (states j).modulus + Real.log α⁻¹ + Real.sqrt (Real.log (states j).size)) ≤
      Real.log (states (j + 1)).size

namespace RecurrencePrefix

def start {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (d Bmax Aq Aδ : ℕ) (c₂ cLength α Clog : ℝ) (initial : RecurrenceState P c s) :
    RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial 0 where
  states := fun _ => initial
  zero := rfl
  steps := by intro j hj; omega
  log_steps := by intro j hj; omega

def extend {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    {d Bmax Aq Aδ n : ℕ} {c₂ cLength α Clog : ℝ} {initial : RecurrenceState P c s}
    (p : RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial n)
    (next : RecurrenceState P c s)
    (hn : RecurrenceStep d Bmax Aq Aδ c₂ cLength (p.states n) next)
    (hlog : (firstDegree P : ℝ) / d * Real.log (p.states n).size -
      Clog * (Real.log (p.states n).modulus + Real.log α⁻¹ + Real.sqrt (Real.log (p.states n).size)) ≤
        Real.log next.size) :
    RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial (n + 1) where
  states := Function.update p.states (n + 1) next
  zero := by rw [Function.update_of_ne (by omega : 0 ≠ n + 1), p.zero]
  steps := by
    intro j hj
    by_cases hjn : j < n
    · rw [Function.update_of_ne (by omega : j ≠ n + 1),
        Function.update_of_ne (by omega : j + 1 ≠ n + 1)]
      exact p.steps j hjn
    · have hjn' : j = n := by omega
      subst j
      rw [Function.update_of_ne (by omega : n ≠ n + 1), Function.update_self]
      exact hn
  log_steps := by
    intro j hj
    by_cases hjn : j < n
    · simp only [Function.update_of_ne (by omega : j ≠ n + 1),
        Function.update_of_ne (by omega : j + 1 ≠ n + 1)]
      exact p.log_steps j hjn
    · have hjn' : j = n := by omega
      subst j
      rw [Function.update_of_ne (by omega : n ≠ n + 1), Function.update_self]
      exact hlog

theorem density_lower {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    {d Bmax Aq Aδ n : ℕ} {c₂ cLength α Clog : ℝ} {initial : RecurrenceState P c s}
    (p : RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial n) (hc₂ : 0 ≤ c₂)
    (j : ℕ) (hj : j ≤ n) : initial.density ≤ (p.states j).density := by
  have hb : 1 ≤ 1 + c₂ := by linarith
  have hpow : 1 ≤ (1 + c₂) ^ j := one_le_pow₀ hb
  have hg := density_growth_lower_bound (fun j => (p.states j).density) (by linarith : 0 ≤ 1 + c₂)
    j (fun k hk => (p.steps k (by omega)).density_growth)
  change (1 + c₂) ^ j * (p.states 0).density ≤ (p.states j).density at hg
  rw [p.zero] at hg
  exact (by nlinarith [initial.density_nonneg] : initial.density ≤
    (1 + c₂) ^ j * initial.density).trans hg

theorem size_upper {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    {d Bmax Aq Aδ n : ℕ} {c₂ cLength α Clog : ℝ} {initial : RecurrenceState P c s}
    (p : RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial n)
    (j : ℕ) (hj : j ≤ n) : (p.states j).size ≤ initial.size := by
  induction j with
  | zero => rw [p.zero]
  | succ j ih =>
    exact ((p.steps j (by omega)).size_nonincrease).trans (ih (by omega))

end RecurrencePrefix

/-- Finite dependent construction. This lemma only extends already-built
prefixes; it does not assume that future numerical ranges are admissible. -/
theorem recurrence_prefix_exists {ℓ : ℕ} {P : PolynomialFamily ℓ} {c : ℝ} {s : ℕ}
    (d Bmax Aq Aδ : ℕ) (c₂ cLength α Clog : ℝ) (initial : RecurrenceState P c s)
    (T : ℕ)
    (hnext : ∀ n < T, ∀ p : RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial n,
      ∃ next : RecurrenceState P c s,
        Nonempty (RecurrenceStep d Bmax Aq Aδ c₂ cLength (p.states n) next) ∧
        (firstDegree P : ℝ) / d * Real.log (p.states n).size -
          Clog * (Real.log (p.states n).modulus + Real.log α⁻¹ + Real.sqrt (Real.log (p.states n).size)) ≤
            Real.log next.size) :
    Nonempty (RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial T) := by
  have hbuild : ∀ n : ℕ, n ≤ T →
      Nonempty (RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial n) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨RecurrencePrefix.start d Bmax Aq Aδ c₂ cLength α Clog initial⟩
    | succ n ih =>
      intro hn
      obtain ⟨p⟩ := ih (by omega)
      obtain ⟨next, ⟨hstep⟩, hlog⟩ := hnext n (by omega) p
      exact ⟨p.extend next hstep hlog⟩
  exact hbuild T le_rfl

/-- Generic constructive iteration of genuine set increments. The density
exponent is chosen before c and before the scale threshold of the step
provider. A later theorem supplies that provider from the primitive sources;
it is not introduced as an external theorem or a main-result axiom. -/
theorem quantitative_recurrence_from_steps {ℓ Adiv : ℕ}
    (P : PolynomialFamily ℓ) (d Bmax Aq Aδ : ℕ) (hd : 1 ≤ d)
    (hrd : firstDegree P ≤ d) (p : KMTTComparisonParameters ℓ Adiv)
    (c₂ cLength : ℝ) (hc₂ : 0 < c₂) (hcLength : 0 < cLength) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c : ℝ, ∀ Nsource : ℕ,
      (∀ s : ℕ, ∀ S : RecurrenceState P c s, Nsource ≤ S.size →
        KMTTAdmissible p S.size S.modulus s S.density →
        ∃ S' : RecurrenceState P c s, Nonempty (RecurrenceStep d Bmax Aq Aδ c₂ cLength S S')) →
      ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset ℤ, A ⊆ integerInterval N →
        (Real.log (N : ℝ)) ^ (-κ) ≤ setDensity N A → ContainsConfiguration P.polynomials c A := by
  classical
  have hr : 1 ≤ firstDegree P := firstDegree_pos P
  have hdr : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hrr : (0 : ℝ) < firstDegree P := by exact_mod_cast (by omega : 0 < firstDegree P)
  have hθ : 0 < (firstDegree P : ℝ) / d := div_pos hrr hdr
  have hθ₁ : (firstDegree P : ℝ) / d ≤ 1 := (div_le_one hdr).mpr (by exact_mod_cast hrd)
  obtain ⟨Clog, hClog, hlogStep⟩ := log_increment_length_lower_bound_initial_density
    d (firstDegree P) Aq Aδ hd hr hrd cLength hcLength
  let β : ℝ := 1 + c₂
  have hβ : 1 < β := by dsimp [β]; linarith
  let J : ℝ := 1 / Real.log β + 1
  let A₀ : ℝ := 2 * p.C₁
  let Hq₀ : ℝ := (p.K₁ + 1) ^ 2
  let Hs : ℝ := p.K₁ + 1
  let H₀ : ℝ := Real.log 2 + Hq₀
  have hA₀ : 0 < A₀ := by dsimp [A₀]; linarith [p.C₁_ge]
  have hHq₀ : 0 ≤ Hq₀ := sq_nonneg _
  have hHs : 0 ≤ Hs := by dsimp [Hs]; linarith [p.K₁_ge]
  have hH₀ : 0 ≤ H₀ := by dsimp [H₀]; exact add_nonneg (Real.log_nonneg (by norm_num)) hHq₀
  have hlogβ : 0 < Real.log β := Real.log_pos hβ
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hν : 0 < (1 / p.C₁ ^ 2 : ℝ) := by have := p.C₁_ge; positivity
  obtain ⟨κ₀, hκ₀, hquant⟩ := quantitative_prefix_admissibility
    ((firstDegree P : ℝ) / d) (Bmax + 1 : ℝ) Clog J A₀ H₀ Hq₀ Hs p.c₀ (1 / p.C₁ ^ 2)
    hθ hθ₁ (by have hB : (0 : ℝ) ≤ Bmax := Nat.cast_nonneg Bmax; linarith) hClog.le hJ hH₀ hHq₀ hHs p.c₀_pos hν
  let κ : ℝ := min κ₀ (1 / (8 * A₀))
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκA : κ * A₀ ≤ 1 / 8 := by
    have hmin : κ ≤ 1 / (8 * A₀) := min_le_right _ _
    calc
      κ * A₀ ≤ (1 / (8 * A₀)) * A₀ := mul_le_mul_of_nonneg_right hmin hA₀.le
      _ = 1 / 8 := by field_simp; ring
  have hhalf := eventually_initial_modulus_half hA₀.le hHq₀ hκA
  refine ⟨κ, hκ, ?_⟩
  intro c Nsource hprovider
  have hlogt : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdom := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hlogt).eventually_ge_atTop
    (max 1 (Real.log ((max 1 Nsource : ℕ) : ℝ)))
  have hfloor := eventually_floorScale_pos (by linarith [p.c₀_lt] : 2 * p.c₀ < 1) d (by omega)
  obtain ⟨Nfloor, hNfloor⟩ := Filter.eventually_atTop.mp hfloor
  have hdomFloor := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hlogt).eventually_ge_atTop
    (Real.log ((max 1 Nfloor : ℕ) : ℝ))
  filter_upwards [hquant, hhalf, hdom, hdomFloor, hlogt.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop 1] with N hquantN hhalfN hdomN hdomFloorN hlogN hN
  intro A hA hthreshold
  by_contra hno
  let α : ℝ := setDensity N A
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogN
  have hα : 0 < α := (Real.rpow_pos_of_pos hlogpos _).trans_le hthreshold
  have hα₁ : α ≤ 1 := by
    apply (div_le_one hNr).mpr
    have := Finset.card_le_card hA
    rw [card_integerInterval] at this
    exact_mod_cast this
  let s : ℕ := ⌈p.K₁ * α ^ (-p.C₁)⌉₊
  let Q₀ : ℕ := smoothModulus s
  have hQ₀ : 0 < Q₀ := smoothModulus_pos s
  have hq₀ : Real.log (Q₀ : ℝ) ≤ Hq₀ * α ^ (-A₀) :=
    initial_modulus_log_bound hα hα₁ (by linarith [p.K₁_ge]) (by linarith [p.C₁_ge])
  have hs : (s : ℝ) ≤ Hs * α ^ (-A₀) :=
    initial_smoothness_upper_common_exponent hα hα₁ (by linarith [p.K₁_ge]) (by linarith [p.C₁_ge])
  have hs₂ : 2 ≤ s := initial_smoothness_lower hα hα₁ p.K₁_ge (by linarith [p.C₁_ge])
  have hQhalf : 2 * Q₀ ≤ N := hhalfN α Q₀ hthreshold (by omega) hq₀
  obtain ⟨r₀, hrlo, hrhi, hn₀, hAsub₀, hδ₀, hsize₀⟩ :=
    exists_initial_residue A N Q₀ hQ₀ (by omega) hA
  let initial : RecurrenceState P c s := {
    size := initialResidueLength N Q₀ r₀
    modulus := Q₀
    set := initialPullback A N Q₀ r₀
    size_pos := hn₀
    modulus_pos := by omega
    subset := hAsub₀
    smooth := smoothModulus_smooth s
    saturated := dvd_refl _
    forbidden := noRescaledConfiguration_of_no_original P.polynomials P.zero_constant c A
      (initialPullback A N Q₀ r₀) Q₀ hQ₀ r₀ (fun u hu => (Finset.mem_filter.mp hu).2) hno }
  have hinitdensity : α ≤ initial.density := hδ₀
  have hinitsize : initial.size ≤ N := by
    have hc := Finset.card_le_card (Finset.filter_subset
      (fun x => initialResidueRepresentative Q₀ x = r₀) (integerInterval N))
    rw [← initialProgression_eq_fiber N Q₀ hQ₀ r₀ hrlo hrhi,
      card_arithmeticProgression _ _ _ hQ₀, card_integerInterval] at hc
    exact hc
  have hinitlog : Real.log (N : ℝ) - H₀ * α ^ (-A₀) ≤ Real.log (initial.size : ℝ) :=
    initial_log_length_bound (by omega) hQ₀
      (initialResidueLength_half_lower N Q₀ hQ₀ hQhalf r₀ hrhi) hα hα₁ hA₀.le hq₀
  have hthreshold₀ : (Real.log (N : ℝ)) ^ (-κ₀) ≤ α := by
    apply le_trans _ hthreshold
    apply Real.rpow_le_rpow_of_exponent_le hlogN
    have := min_le_left κ₀ (1 / (8 * A₀))
    change κ ≤ κ₀ at this
    linarith
  let T : ℕ := ⌊Real.log α⁻¹ / Real.log β⌋₊ + 1
  obtain ⟨hTupper, hTlarge⟩ := density_horizon_bounds hα hα₁ hβ
  have hTupper' : (T : ℝ) ≤ J * (Real.log α⁻¹ + 1) := hTupper
  have hcurrent : ∀ n ≤ T,
      ∀ pref : RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial n,
        KMTTAdmissible p (pref.states n).size (pref.states n).modulus s (pref.states n).density ∧
        Nsource ≤ (pref.states n).size ∧
        1 ≤ Real.log ((pref.states n).size : ℝ) ∧
        1 ≤ floorScale (pref.states n).size (pref.states n).modulus d := by
    intro n hn pref
    have hαδ : α ≤ (pref.states n).density := hinitdensity.trans (pref.density_lower hc₂.le n le_rfl)
    have hnum := hquantN α (pref.states n).density
      (fun j => (pref.states j).size) (fun j => (pref.states j).modulus) s n n hα hα₁
      hthreshold₀ hαδ hs ((by exact_mod_cast hn : (n : ℝ) ≤ T).trans hTupper')
      (fun j _ => (pref.states j).modulus_pos)
      (by simpa only [pref.zero] using hq₀) (by simpa only [pref.zero] using hinitlog)
      (fun j hj => by
        change Real.log ((pref.states (j + 1)).modulus : ℝ) ≤
          (Bmax + 1 : ℝ) * Real.log ((pref.states j).modulus : ℝ)
        rw [(pref.steps j hj).modulus_update, Nat.cast_pow, Real.log_pow]
        apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
        exact_mod_cast (Nat.add_le_add_right (pref.steps j hj).exponent_le 1))
      (fun j hj => Real.log_le_log (by exact_mod_cast (by have := (pref.states j).size_pos; omega : 0 < (pref.states j).size))
        (by exact_mod_cast (pref.size_upper j (by omega)).trans hinitsize))
      pref.log_steps le_rfl
    obtain ⟨hloglower, hQupper, hsupper, hδlower⟩ := hnum
    have hlog₁ : 1 ≤ Real.log ((pref.states n).size : ℝ) :=
      ((le_max_left _ _).trans hdomN).trans hloglower
    have hstage : Nsource ≤ (pref.states n).size := by
      have hlogsource : Real.log ((max 1 Nsource : ℕ) : ℝ) ≤ Real.log ((pref.states n).size : ℝ) :=
        ((le_max_right _ _).trans hdomN).trans hloglower
      have hreal := (Real.log_le_log_iff (by positivity : (0 : ℝ) < (max 1 Nsource : ℕ))
        (by exact_mod_cast (by have := (pref.states n).size_pos; omega : 0 < (pref.states n).size))).mp hlogsource
      have hnat : max 1 Nsource ≤ (pref.states n).size := by exact_mod_cast hreal
      omega
    have hstageFloor : Nfloor ≤ (pref.states n).size := by
      have hlogfloor := hdomFloorN.trans hloglower
      have hreal := (Real.log_le_log_iff (by positivity : (0 : ℝ) < (max 1 Nfloor : ℕ))
        (by exact_mod_cast (by have := (pref.states n).size_pos; omega : 0 < (pref.states n).size))).mp hlogfloor
      have hnat : max 1 Nfloor ≤ (pref.states n).size := by exact_mod_cast hreal
      omega
    refine ⟨⟨(pref.states n).modulus_pos, hs₂, hδlower, (pref.states n).density_le_one,
      ?_, hsupper, hQupper, (pref.states n).smooth, (pref.states n).saturated⟩,
      hstage, hlog₁, ?_⟩
    · exact smoothness_requirement_mono hα hαδ (by linarith [p.K₁_ge]) (by linarith [p.C₁_ge])
    · exact hNfloor _ hstageFloor _ (pref.states n).modulus_pos hQupper
  have hprefix : Nonempty (RecurrencePrefix d Bmax Aq Aδ c₂ cLength α Clog initial T) := by
    apply recurrence_prefix_exists
    intro n hn pref
    obtain ⟨hadm, hstage, hlog₁, hM⟩ := hcurrent n (by omega) pref
    obtain ⟨next, ⟨hstep⟩⟩ := hprovider s (pref.states n) hstage hadm
    refine ⟨next, ⟨hstep⟩, ?_⟩
    exact hlogStep (pref.states n).size (pref.states n).modulus next.size
      (pref.states n).size_pos (pref.states n).modulus_pos hM hlog₁ α (pref.states n).density
      hα (hinitdensity.trans (pref.density_lower hc₂.le n le_rfl)) (pref.states n).density_le_one
      hstep.length_lower
  obtain ⟨pref⟩ := hprefix
  apply density_growth_contradiction (fun j => (pref.states j).density) (by dsimp [β] at hβ; linarith : 0 ≤ 1 + c₂)
    T (fun j hj => (pref.steps j hj).density_growth) (pref.states T).density_le_one
  rw [pref.zero]
  exact hTlarge.trans_le (mul_le_mul_of_nonneg_left hinitdensity (pow_nonneg (by linarith) _))

end PSPrimes
