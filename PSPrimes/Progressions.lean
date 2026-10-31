import PSPrimes.ExternalInputs

/-!
# Finite Fourier restriction to progressions

These checked finite identities are supporting results for manuscript Lemma 2.2.
They do not assert its quantitative polynomial-phase estimate.
-/

noncomputable section
open scoped BigOperators

namespace PSPrimes

/-- Additive character orthogonality for the class 1 modulo a positive modulus. -/
theorem congruenceIndicator_fourier (Q : ℕ) [NeZero Q] (n : ℕ) :
    (if (n : ZMod Q) = 1 then (1 : ℂ) else 0) =
      (Q : ℂ)⁻¹ * ∑ a : ZMod Q, ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar Q)]
  by_cases h : (n : ZMod Q) = 1
  · simp [h, ZMod.card, NeZero.ne Q]
  · simp [sub_eq_zero, h]

/-- Exact Fourier projection of a finite sum onto one residue class. -/
theorem residueSum_fourier (Q : ℕ) [NeZero Q] (s : Finset ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ s.filter (fun n : ℕ => (n : ZMod Q) = 1), f n =
      (Q : ℂ)⁻¹ * ∑ a : ZMod Q, ∑ n ∈ s,
        ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n := by
  classical
  simp only [Finset.sum_filter]
  calc
    ∑ n ∈ s, (if (n : ZMod Q) = 1 then f n else 0) =
        ∑ n ∈ s, (if (n : ZMod Q) = 1 then (1 : ℂ) else 0) * f n := by
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ n ∈ s, ((Q : ℂ)⁻¹ *
        ∑ a : ZMod Q, ZMod.stdAddChar (a * ((n : ZMod Q) - 1))) * f n := by
      simp_rw [congruenceIndicator_fourier]
    _ = (Q : ℂ)⁻¹ * ∑ a : ZMod Q, ∑ n ∈ s,
        ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n := by
      simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Averaging Q uniformly bounded character sums does not lose a factor Q. -/
theorem norm_residueSum_le (Q : ℕ) [NeZero Q] (s : Finset ℕ) (f : ℕ → ℂ)
    (E : ℝ) (hE : ∀ a : ZMod Q,
      ‖∑ n ∈ s, ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n‖ ≤ E) :
    ‖∑ n ∈ s.filter (fun n : ℕ => (n : ZMod Q) = 1), f n‖ ≤ E := by
  rw [residueSum_fourier, norm_mul]
  calc
    ‖(Q : ℂ)⁻¹‖ * ‖∑ a : ZMod Q, ∑ n ∈ s,
        ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n‖ ≤
        ‖(Q : ℂ)⁻¹‖ * ∑ a : ZMod Q,
          ‖∑ n ∈ s, ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(Q : ℂ)⁻¹‖ * ∑ _a : ZMod Q, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hE a)) (norm_nonneg _)
    _ = E := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        norm_inv, Complex.norm_natCast]
      have hQ : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
      field_simp

/-- Exact reindexing, including the initial representative n=1. -/
theorem progressionSum_reindex_zero (Q M : ℕ) [NeZero Q] (f : ℕ → ℂ) :
    (∑ y ∈ Finset.Icc 0 M, f (Q * y + 1)) =
      ∑ n ∈ (Finset.Icc 1 (Q * M + 1)).filter
        (fun n : ℕ => (n : ZMod Q) = 1), f n := by
  classical
  have hQ : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  refine Finset.sum_bij (fun y _ => Q * y + 1) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_Icc] at hy
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor
      · omega
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left Q hy.2) 1
    · simp
  · intro y hy z hz h
    dsimp at h
    have : Q * y = Q * z := by omega
    exact Nat.eq_of_mul_eq_mul_left hQ this
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hz : ((n - 1 : ℕ) : ZMod Q) = 0 := by
      rw [Nat.cast_sub hn.1.1, Nat.cast_one, hn.2]
      simp
    obtain ⟨y, hy⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd (n - 1) Q).mp hz
    have hn' : n = Q * y + 1 := by omega
    refine ⟨y, Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, hn'.symm⟩
    have hmul : Q * y ≤ Q * M := by omega
    exact Nat.le_of_mul_le_mul_left hmul hQ
  · intro y hy
    rfl

/-- The manuscript's positive-interval reindexing: the omitted n=1 term is zero. -/
theorem progressionSum_reindex (Q M : ℕ) [NeZero Q] (f : ℕ → ℂ) (hf : f 1 = 0) :
    (∑ y ∈ Finset.Icc 1 M, f (Q * y + 1)) =
      ∑ n ∈ (Finset.Icc 1 (Q * M + 1)).filter
        (fun n : ℕ => (n : ZMod Q) = 1), f n := by
  classical
  rw [← progressionSum_reindex_zero]
  apply Finset.sum_subset
  · intro y hy
    simp only [Finset.mem_Icc] at hy ⊢
    exact ⟨Nat.zero_le _, hy.2⟩
  · intro y hy hnot
    simp only [Finset.mem_Icc] at hy hnot
    have hy0 : y = 0 := by omega
    simp [hy0, hf]

/-- Progression restriction as an average of full-interval character twists. -/
theorem progressionSum_fourier (Q M : ℕ) [NeZero Q] (f : ℕ → ℂ) (hf : f 1 = 0) :
    (∑ y ∈ Finset.Icc 1 M, f (Q * y + 1)) =
      (Q : ℂ)⁻¹ * ∑ a : ZMod Q, ∑ n ∈ Finset.Icc 1 (Q * M + 1),
        ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n := by
  rw [progressionSum_reindex Q M f hf, residueSum_fourier]

/-- Exact bound after progression restriction, with no modulus factor. -/
theorem norm_progressionSum_le (Q M : ℕ) [NeZero Q] (f : ℕ → ℂ)
    (hf : f 1 = 0) (E : ℝ) (hE : ∀ a : ZMod Q,
      ‖∑ n ∈ Finset.Icc 1 (Q * M + 1),
        ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n‖ ≤ E) :
    ‖∑ y ∈ Finset.Icc 1 M, f (Q * y + 1)‖ ≤ E := by
  rw [progressionSum_reindex Q M f hf]
  exact norm_residueSum_le Q _ f E hE

/-- The actual real-coefficient phase represented by each residue character. -/
theorem stdAddChar_progression (Q : ℕ) [NeZero Q] (a : ZMod Q) (n : ℕ) :
    ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) =
      complexPhase ((a.val : ℝ) * ((n : ℝ) - 1) / (Q : ℝ)) := by
  have hz : a * ((n : ZMod Q) - 1) =
      (((a.val : ℤ) * ((n : ℤ) - 1) : ℤ) : ZMod Q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hz, ZMod.stdAddChar_coe]
  unfold complexPhase
  congr 1
  push_cast
  ring

theorem complexPhase_add (s t : ℝ) :
    complexPhase (s + t) = complexPhase s * complexPhase t := by
  unfold complexPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Coefficient-uniform polynomial-phase bounds restrict to every progression.
This proves the finite Fourier restriction step of manuscript Lemma 2.2;
the bound is evaluated at QM+1, before the elementary power comparison. -/
theorem PhaseBound.progression {r Q M : ℕ} [NeZero Q] (hr : 1 ≤ r)
    {w : ℕ → ℂ} {E : ℝ} (hw : w 1 = 0)
    (h : PhaseBound r (Q * M + 1) w E) :
    PhaseBound r M (fun y => w (Q * y + 1)) E := by
  classical
  intro ψ hψ
  let η : Polynomial ℝ := Polynomial.C (Q : ℝ)⁻¹ * (Polynomial.X - 1)
  let f : ℕ → ℂ := fun n => w n * complexPhase
    (ψ.eval ((Q : ℝ)⁻¹ * ((n : ℝ) - 1)))
  have hQ : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
  have hη : η.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hηeval (y : ℕ) : (Q : ℝ)⁻¹ * (((Q * y + 1 : ℕ) : ℝ) - 1) = y := by
    push_cast
    field_simp
  have hbound : ‖∑ y ∈ Finset.Icc 1 M, f (Q * y + 1)‖ ≤ E := by
    apply norm_progressionSum_le Q M f (by simp [f, hw]) E
    intro a
    let φ : Polynomial ℝ := ψ.comp η +
      Polynomial.C ((a.val : ℝ) / (Q : ℝ)) * (Polynomial.X - 1)
    have hφ : φ.natDegree ≤ r := by
      apply Polynomial.natDegree_add_le_of_degree_le
      · exact Polynomial.natDegree_comp_le.trans
          ((Nat.mul_le_mul hψ hη).trans (by simp))
      · exact (Polynomial.natDegree_C_mul_le _ _).trans
          ((Polynomial.natDegree_sub_le _ _).trans ((by simp :
            max (Polynomial.X : Polynomial ℝ).natDegree (1 : Polynomial ℝ).natDegree ≤ 1).trans hr))
    have heq : (∑ n ∈ Finset.Icc 1 (Q * M + 1),
        ZMod.stdAddChar (a * ((n : ZMod Q) - 1)) * f n) =
        phaseSum (Q * M + 1) w φ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [stdAddChar_progression]
      simp only [f, φ, η, Polynomial.eval_add, Polynomial.eval_comp,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one, complexPhase_add]
      have ha : (a.val : ℝ) * ((n : ℝ) - 1) / (Q : ℝ) =
          ((a.val : ℝ) / (Q : ℝ)) * ((n : ℝ) - 1) := by ring
      rw [ha]
      ring
    rw [heq]
    exact h φ hφ
  convert hbound using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro y hy
  change w (Q * y + 1) * complexPhase (ψ.eval (y : ℝ)) = f (Q * y + 1)
  dsimp only [f]
  rw [hηeval]

/-- The endpoint shift from L to L+1 costs at most 2 for an exponent in [0,1]. -/
theorem rpow_add_one_le_two_mul {L t : ℝ} (hL : 1 ≤ L)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (L + 1) ^ t ≤ 2 * L ^ t := by
  calc
    (L + 1) ^ t ≤ (2 * L) ^ t :=
      Real.rpow_le_rpow (by linarith) (by linarith) ht₀
    _ = (2 : ℝ) ^ t * L ^ t := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 2 * L ^ t := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ht₁

/-- Manuscript Lemma 2.2, conditional only on the quoted coefficient-uniform
Shao--Sun polynomial-phase input. The range ε and saving σ are chosen before γ;
the constant is uniform in Q, M and all phase coefficients. The saving may be
shrunk to at most 1/2, without changing the assertion of the manuscript. -/
theorem progressionPhase_of_shaoSun (hSS : ShaoSunPhaseInput) :
    ∀ r : ℕ, 1 ≤ r → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ σ : ℝ, 0 < σ ∧ ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
        ∃ C : ℝ, 0 < C ∧ ∀ Q M : ℕ, 1 ≤ Q → 1 ≤ M →
          PhaseBound r M (fun y => (discrepancyWeight γ (Q * y + 1) : ℂ))
            (C * ((Q * M : ℕ) : ℝ) ^ (1 - σ)) := by
  intro r hr
  obtain ⟨ε, hε₀, hε₁, σ, hσ₀, hσ⟩ := hSS r hr
  refine ⟨ε, hε₀, hε₁, min σ (1 / 2), lt_min hσ₀ (by norm_num), ?_⟩
  intro γ hγ₀ hγ₁
  obtain ⟨C, hC₀, hC⟩ := hσ γ hγ₀ hγ₁
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q M hQ hM
  letI : NeZero Q := ⟨by omega⟩
  have hLnat : 1 ≤ Q * M := by nlinarith
  have hL : (1 : ℝ) ≤ ((Q * M : ℕ) : ℝ) := by exact_mod_cast hLnat
  have hx : (1 : ℝ) ≤ ((Q * M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q * M + 1)
  have hp := (hC (Q * M + 1) (by omega)).progression hr
    (by simp : (discrepancyWeight γ 1 : ℂ) = 0)
  intro ψ hψ
  calc
    ‖phaseSum M (fun y => (discrepancyWeight γ (Q * y + 1) : ℂ)) ψ‖ ≤
        C * ((Q * M + 1 : ℕ) : ℝ) ^ (1 - σ) := hp ψ hψ
    _ ≤ C * ((Q * M + 1 : ℕ) : ℝ) ^ (1 - min σ (1 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      apply Real.rpow_le_rpow_of_exponent_le hx
      linarith [min_le_left σ (1 / 2 : ℝ)]
    _ ≤ C * (2 * ((Q * M : ℕ) : ℝ) ^ (1 - min σ (1 / 2))) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      rw [Nat.cast_add, Nat.cast_one]
      apply rpow_add_one_le_two_mul hL
      · linarith [min_le_right σ (1 / 2 : ℝ)]
      · have hm : 0 < min σ (1 / 2 : ℝ) := lt_min hσ₀ (by norm_num)
        linarith
    _ = (2 * C) * ((Q * M : ℕ) : ℝ) ^ (1 - min σ (1 / 2)) := by ring

end PSPrimes
