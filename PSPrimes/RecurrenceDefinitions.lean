import PSPrimes.Definitions
import PSPrimes.Density
import PSPrimes.Scales

/-! Exact finite objects used in the KMTT recurrence inputs. -/
noncomputable section
open scoped BigOperators
namespace PSPrimes

/-- The spatial interval consists of integers, not a cyclic group. -/
def integerInterval (N : ℕ) : Finset ℤ := Finset.Icc 1 (N : ℤ)

@[simp] theorem card_integerInterval (N : ℕ) : (integerInterval N).card = N := by
  simp [integerInterval]

theorem integerInterval_nonempty {N : ℕ} (hN : 1 ≤ N) :
    (integerInterval N).Nonempty := by
  exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hN⟩⟩

/-- Arithmetic progression with positive-index convention `a+q[1,L]`. -/
def arithmeticProgression (a : ℤ) (q L : ℕ) : Finset ℤ :=
  (integerInterval L).image (fun x => a + (q : ℤ) * x)

@[simp] theorem card_arithmeticProgression (a : ℤ) (q L : ℕ) (hq : 0 < q) :
    (arithmeticProgression a q L).card = L := by
  rw [arithmeticProgression, Finset.card_image_of_injective]
  · exact card_integerInterval L
  · intro x y h
    exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hq) : (q : ℤ) ≠ 0)
      (add_left_cancel h)

/-- Definition 2.2 of KMTT, with the coefficient and degree conditions explicit. -/
def HasCQCoefficients (C : ℝ) (Q : ℕ) (P : Polynomial ℤ) : Prop :=
  P.coeff 0 = 0 ∧ 1 ≤ P.natDegree ∧
    ∃ a : ℤ, P.coeff P.natDegree = a * (Q : ℤ) ^ (P.natDegree - 1) ∧
      0 < |a| ∧ (|a| : ℝ) ≤ C ∧
      ∀ j : ℕ, 1 ≤ j → j < P.natDegree →
        (|P.coeff j| : ℝ) ≤ C * (|P.coeff P.natDegree| : ℝ)

/-- The zeroth shift is zero; the remaining entries are the actual polynomials. -/
def recurrencePolynomials {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) :
    Fin (ℓ + 1) → Polynomial ℤ := Fin.cons 0 P

/-- The whole `ℓ+1` factor counting form, with original `N M` normalization.
When the zeroth factor is supported on `[N]`, the unrestricted integer sum
in the source is exactly this finite sum. -/
def realConfigurationForm {ℓ : ℕ} (N M Q : ℕ) (P : Fin ℓ → Polynomial ℤ)
    (w : ℕ → ℝ) (f : Fin (ℓ + 1) → ℤ → ℝ) : ℝ :=
  ((N : ℝ) * (M : ℝ))⁻¹ *
    ∑ y ∈ initialInterval M, ∑ x ∈ integerInterval N,
      w (Q * y + 1) * ∏ i, f i (x + (recurrencePolynomials P i).eval (y : ℤ))

def realIndicator (A : Finset ℤ) (a : ℝ) (x : ℤ) : ℝ := if x ∈ A then a else 0

def realSetCount {ℓ : ℕ} (N M Q : ℕ) (P : Fin ℓ → Polynomial ℤ)
    (w : ℕ → ℝ) (A : Finset ℤ) : ℝ :=
  realConfigurationForm N M Q P w (fun _ => realIndicator A 1)

def realModelCount {ℓ : ℕ} (N M Q : ℕ) (P : Fin ℓ → Polynomial ℤ)
    (w : ℕ → ℝ) (δ : ℝ) : ℝ :=
  realConfigurationForm N M Q P w (fun _ => realIndicator (integerInterval N) δ)

def primeProgressionMass (Q M : ℕ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ y ∈ initialInterval M, ArithmeticFunction.vonMangoldt (Q * y + 1)

/-- A genuine finite local factor. Resolution is the cardinality of an
arithmetic-progression atom, not its diameter. -/
structure ArithmeticLocalFactor (N q : ℕ) where
  resolution : ℕ
  resolution_pos : 1 ≤ resolution
  cells : Finset (Finset ℤ)
  cover : cells.biUnion id = integerInterval N
  disjoint : (cells : Set (Finset ℤ)).PairwiseDisjoint id
  atoms_nonempty : ∀ B ∈ cells, B.Nonempty
  atoms_progressions : ∀ B ∈ cells, ∃ a : ℤ, ∃ L : ℕ,
    B = arithmeticProgression a q L ∧ resolution ≤ L ∧ L ≤ 2 * resolution

def cellMean (B : Finset ℤ) (f : ℤ → ℝ) : ℝ :=
  (B.card : ℝ)⁻¹ * ∑ x ∈ B, f x

/-- This relation fixes every value of the zero-extended conditional average.
It is used as an output of the externally quoted regularity theorem. -/
def IsLocalProjection {N q : ℕ} (B : ArithmeticLocalFactor N q)
    (f F : ℤ → ℝ) : Prop :=
  (∀ x ∉ integerInterval N, F x = 0) ∧
    ∀ atom ∈ B.cells, ∀ x ∈ atom, F x = cellMean atom f

theorem cellMean_indicator (A B : Finset ℤ) :
    cellMean B (realIndicator A 1) = atomDensity A B := by
  classical
  simp only [cellMean, realIndicator, Finset.sum_boole, atomDensity]
  have hfilter : B.filter (fun x => x ∈ A) = A ∩ B := by
    ext x
    simp [and_comm]
  rw [hfilter]
  ring

theorem ArithmeticLocalFactor.atom_subset {N q : ℕ} (B : ArithmeticLocalFactor N q)
    {atom : Finset ℤ} (hatom : atom ∈ B.cells) : atom ⊆ integerInterval N := by
  intro x hx
  rw [← B.cover]
  exact Finset.mem_biUnion.mpr ⟨atom, hatom, hx⟩

theorem ArithmeticLocalFactor.atom_length {N q : ℕ} (B : ArithmeticLocalFactor N q)
    (hq : 0 < q) {atom : Finset ℤ} (hatom : atom ∈ B.cells) :
    B.resolution ≤ atom.card := by
  obtain ⟨a, L, rfl, hL, _⟩ := B.atoms_progressions atom hatom
  simpa only [card_arithmeticProgression a q L hq] using hL

end PSPrimes
