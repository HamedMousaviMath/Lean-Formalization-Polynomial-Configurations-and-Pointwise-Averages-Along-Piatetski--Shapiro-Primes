import PSPrimes.KMTTInterfaces

/-!
# Explicit compatible prime-progression mass inputs

These are uninstantiated external data from the classical estimates in the
proofs of KMTT (arXiv:2608.19525v1), equations (5.2) and (5.15). They do not
assume a polynomial count or a Piatetski--Shapiro discrepancy conclusion.

The cutoff and its constants are selected for fixed source parameters. In
particular this interface does not assert a mass fraction uniform as the
cutoff tends to zero. The compatibility with the SAME source discrepancy
constant c₁ is explicit: a witness is to be selected jointly with the KMTT
comparison parameters, never asserted for arbitrary parameter records.
-/

noncomputable section
open scoped BigOperators
namespace PSPrimes

/-- The two classical mass estimates, with source-compatible c₁ and one fixed
small cutoff. `τmax` is a previously fixed elementary coefficient cutoff.
The source-to-interface selection of compatible constants is external and
must be included in any joint existence hypothesis using this witness. -/
structure PrimeProgressionMassWitness {ℓ Adiv : ℕ}
    (p : KMTTComparisonParameters ℓ Adiv) (d : ℕ) (τmax : ℝ) where
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  cutoff_le_one : cutoff ≤ 1
  cutoff_le : cutoff ≤ τmax
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  exponentConstant : ℝ
  exponentConstant_pos : 0 < exponentConstant
  threshold : ℕ
  truncated_mass : ∀ N Q s : ℕ, ∀ δ : ℝ,
    threshold ≤ N → KMTTAdmissible p N Q s δ →
    (4 * p.c₁) *
      (∑ y ∈ initialInterval (floorScale N Q d), ArithmeticFunction.vonMangoldt (Q * y + 1)) ≤
      ∑ y ∈ initialInterval ⌊cutoff * (floorScale N Q d : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt (Q * y + 1)
  full_mass : ∀ N Q s : ℕ, ∀ δ : ℝ,
    threshold ≤ N → KMTTAdmissible p N Q s δ →
    lowerConstant * Real.exp (-exponentConstant * (Real.log N) ^ (2 * p.c₀)) ≤
      primeProgressionMass Q (floorScale N Q d)

/-- Explicit external joint selection of the SAME comparison and mass data.
The fixed positive coefficient cutoff is selected before `p`. Its additional
constant-selection and reparameterization bridge is documented as KM-J;
this is not a consequence of separate existential comparison and mass inputs.
No inhabitant is supplied here. -/
def KMTTCompatibleInput : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ d ℓ : ℕ, 1 ≤ d → 1 ≤ ℓ → ∀ Adiv : ℕ,
    ∀ τmax : ℝ, 0 < τmax →
      ∃ p : KMTTComparisonParameters ℓ Adiv,
        KMTTUnweightedWitness C d ℓ Adiv p ∧
        Nonempty (PrimeProgressionMassWitness p d τmax)

end PSPrimes
