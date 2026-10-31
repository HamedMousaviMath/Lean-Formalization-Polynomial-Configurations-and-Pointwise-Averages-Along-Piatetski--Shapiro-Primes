import PSPrimes.RecurrenceDefinitions
import PSPrimes.SmoothModuli

/-!
# Two separately quoted KMTT inputs

The source is arXiv:2608.19525v1, Proposition 5.2 and Lemma 5.3.
These propositions are uninstantiated external hypotheses. No density
increment or conclusion of the supplied manuscript is assumed.

The typed interfaces specialize the source to real-valued observables,
integer cutoffs and the explicit finite form. The source-to-interface
finite-support and real-average normalization bridges remain external.
-/
noncomputable section
open scoped BigOperators
namespace PSPrimes

/-- Compatible constants selected once in KMTT (5.7), (5.8), (5.35).
`Adiv` is the regularity divisibility exponent, chosen before these constants.
The source explicitly permits the last two enlargements. -/
structure KMTTComparisonParameters (ℓ Adiv : ℕ) where
  C₁ : ℝ
  K₁ : ℝ
  c₀ : ℝ
  c₁ : ℝ
  C₁_ge : 2 ≤ C₁
  K₁_ge : 2 ≤ K₁
  c₀_pos : 0 < c₀
  c₀_lt : c₀ < 1 / 2
  c₁_pos : 0 < c₁
  c₁_le : c₁ ≤ 1
  divisibility_exponent : (3 * (ℓ + 1) * Adiv : ℝ) ≤ C₁
  divisibility_constant : (16 / c₁) ^ Adiv + 1 ≤ K₁

/-- The exact varying-parameter range of KMTT Proposition 5.2.
`SmoothUpTo` equals the paper's largest-prime-factor bound when `s≥2`. -/
def KMTTAdmissible {ℓ Adiv : ℕ} (p : KMTTComparisonParameters ℓ Adiv)
    (N Q s : ℕ) (δ : ℝ) : Prop :=
  1 ≤ Q ∧ 2 ≤ s ∧
  (Real.log N) ^ (-(1 / p.C₁ ^ 2)) < δ ∧ δ ≤ 1 ∧
  ⌈p.K₁ * δ ^ (-p.C₁)⌉₊ ≤ s ∧ (s : ℝ) ≤ (Real.log N) ^ p.c₀ ∧
  (Q : ℝ) ≤ Real.exp ((Real.log N) ^ (2 * p.c₀)) ∧
  SmoothUpTo s Q ∧ smoothModulus s ∣ Q

/-- Primitive unweighted-discrepancy result: Proposition 5.2, (5.9)-(5.12).
The conclusion is a discrepancy, not a denser progression. -/
def KMTTUnweightedWitness (C : ℝ) (d ℓ Adiv : ℕ)
    (p : KMTTComparisonParameters ℓ Adiv) : Prop :=
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
      ∃ M₀ : ℕ,
        ⌈(floorScale N Q d : ℝ) *
          Real.exp (-Real.sqrt (Real.log (floorScale N Q d : ℝ)))⌉₊ ≤ M₀ ∧
        M₀ ≤ floorScale N Q d ∧
        p.c₁ * δ ^ (ℓ + 1) / 4 ≤
          |realSetCount N M₀ Q R.polynomials (fun _ => 1) A -
            realModelCount N M₀ Q R.polynomials (fun _ => 1) δ|

/-- External Proposition 5.2 with the source's permitted compatibility
choices (5.35). No inhabitant of this proposition is supplied by the project. -/
def KMTTUnweightedInput : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ d ℓ : ℕ, 1 ≤ d → 1 ≤ ℓ → ∀ Adiv : ℕ,
    ∃ p : KMTTComparisonParameters ℓ Adiv, KMTTUnweightedWitness C d ℓ Adiv p

/-- The exponent at coordinate zero is the smallest positive degree, not zero. -/
def firstDegree {ℓ : ℕ} (R : PolynomialFamily ℓ) : ℕ :=
  (R.polynomials ⟨0, R.nonempty⟩).natDegree

def coordinateDegrees {ℓ : ℕ} (R : PolynomialFamily ℓ) : Fin (ℓ + 1) → ℕ :=
  Fin.cons (firstDegree R) (fun i => (R.polynomials i).natDegree)

theorem firstDegree_pos {ℓ : ℕ} (R : PolynomialFamily ℓ) : 1 ≤ firstDegree R :=
  R.positive_degree _

theorem firstDegree_le_coordinate {ℓ : ℕ} (R : PolynomialFamily ℓ)
    (i : Fin (ℓ + 1)) : firstDegree R ≤ coordinateDegrees R i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact le_rfl
  · exact R.increasing_degrees.monotone (show (⟨0, R.nonempty⟩ : Fin ℓ) ≤ j from
      Fin.le_iff_val_le_val.mpr (Nat.zero_le _))

/-- The literal weak-regularity alternative of Lemma 5.3. The exponents
`Aq,Aε,T` are chosen in terms of `d,ℓ` before `C`. Its positive implicit
constants may depend on `C,d,ℓ`. `Bmax` is chosen from `d` before `ℓ,C`.
The approximation is tested against arbitrary real observables, not just the
indicator tuple needed in the current paper. -/
structure KMTTRegularityWitness (C : ℝ) (d ℓ Bmax Aq Aε T : ℕ) where
  Adiv : ℕ
  Adiv_pos : 1 ≤ Adiv
  smallConstant : ℝ
  smallConstant_pos : 0 < smallConstant
  resolutionConstant : ℝ
  resolutionConstant_pos : 0 < resolutionConstant
  regularity : ∀ N Q M₀ : ℕ, 1 ≤ N → 1 ≤ Q → 1 ≤ M₀ →
    (M₀ : ℝ) ≤ rootScale N Q d →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      smoothModulus ⌈ε ^ (-(Adiv : ℝ))⌉₊ ∣ Q →
      ∀ R : PolynomialFamily ℓ,
        (∀ i, HasCQCoefficients C Q (R.polynomials i)) →
        (∀ i, (R.polynomials i).natDegree ≤ d) →
        (∃ i, (R.polynomials i).natDegree = d) →
        ∀ f : Fin (ℓ + 1) → ℤ → ℝ,
          (∀ i x, |f i x| ≤ 1) →
          (∀ i x, x ∉ integerInterval N → f i x = 0) →
          ((M₀ : ℝ) ≤ smallConstant * ((Q : ℝ) / ε) ^ T) ∨
          ∃ b : ℕ, 1 ≤ b ∧ b ≤ Bmax ∧
            ∃ factors : Fin (ℓ + 1) → ArithmeticLocalFactor N (Q ^ b),
            ∃ F : Fin (ℓ + 1) → ℤ → ℝ,
              (∀ i, IsLocalProjection (factors i) (f i) (F i)) ∧
              (∀ i, resolutionConstant * (Q : ℝ) ^ (-(Aq : ℝ)) * ε ^ Aε *
                (M₀ : ℝ) ^ coordinateDegrees R i ≤ (factors i).resolution) ∧
              |realConfigurationForm N M₀ Q R.polynomials (fun _ => 1) f -
                realConfigurationForm N M₀ Q R.polynomials (fun _ => 1) F| ≤ ε

/-- Source Lemma 5.3 with its parameter dependencies made explicit.
Integer exponents are harmless weakenings of positive real O-exponents on
`Q≥1`, `0<ε<1/2`; that specialization is part of the quoted interface. -/
def KMTTRegularityInput : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ Bmax : ℕ, 1 ≤ Bmax ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ Aq Aε T : ℕ, 1 ≤ Aq ∧ 1 ≤ Aε ∧ 1 ≤ T ∧
      ∀ C : ℝ, 1 ≤ C → Nonempty (KMTTRegularityWitness C d ℓ Bmax Aq Aε T)

end PSPrimes
