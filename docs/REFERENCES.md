# External-reference verification — 30 October 2026

This is a source-verification record, not a Lean proof or a proof of an external theorem. All checks below used primary sources. The supplied manuscript was read for its intended interfaces. URLs identify exact versions; no attribution relies on a search snippet. No cited theorem was found to be inaccessible after following the arXiv abstract-page links.

## SS — Shao–Sun

Primary: Xuancheng Shao and Yu-Chen Sun, *Linear equations in Piatetski–Shapiro primes*, [arXiv:2605.18676v1](https://arxiv.org/html/2605.18676v1), 18 May 2026.

Verified Theorem 2.1: a filtered nilmanifold of degree d and dimension D, complexity at most δ⁻¹, and a Lipschitz function of norm at most δ⁻¹ satisfy the stated Λγ−Λ discorrelation estimate with error O_{d,D}(δ^{-O_{d,D}(1)} N^{1-c_{d,D}}), provided 1−γ is sufficiently small in terms of d,D. It applies to every adapted polynomial sequence, with no coefficient-size restriction. Its Λγ is exactly γ⁻¹ n^{1−γ}Λ(n)1_{PS_{1/γ}}(n).

Verified Definition 4.5: adapted polynomial sequences have binomial-coordinate form with the j-th coefficient in the j-th filtration group. Definition 4.4 supplies the filtered-nilmanifold data.

The source explicitly prints an **unnumbered polynomial-phase corollary immediately after Theorem 2.1**. It states the actual discrepancy estimate uniformly over real polynomial coefficients for N≥3. The project directly quotes this published consequence as `ShaoSunPhaseInput`; it does not need to reconstruct the circle/binomial construction to justify that choice of external interface. The general nilsequence theorem remains unformalized optional background. The degree-bound/integer-cutoff specialization and finite extension to X=1,2 are included in the external translation SS-finiteX, not claimed separately checked.

Depends into: manuscript t:shao-sun, l:progression-phase, p:comparison, l:PS-discrepancy, t:szemeredi, p:pointwise-comparison, t:pointwise.

## TV — Teräväinen

Primary: Joni Teräväinen, *Pointwise convergence of ergodic averages with Möbius weight*, [arXiv:2401.03174v2](https://arxiv.org/html/2401.03174v2), 2 August 2024.

Verified Theorem 4.1: distinct increasing integer-polynomial degrees, largest degree d; 1-bounded inputs supported in [−CN^d,CN^d]; 1-bounded θ on [N]; normalization N^{−d−1}. The bound is an implied constant depending on C and the polynomial family times (N⁻¹+‖θ‖_{u^{d+1}[N]})^{1/K}, with 1≤K≪_d1. Thus manuscript t:teravainen faithfully restates it after renaming N to M. The source allows nonzero constant coefficients.

The theorem gives no coefficient-uniform implied constant for changing polynomial families. The manuscript's lift back to fixed P_i is therefore essential. Scaling θ=g/B and the finite lifting identity are separate deductions to prove, not additional content of the quotation.

Lean dependencies: Proposition 2.3, Lemma 3.2 and Theorem 1.1, and now also the derived orbit bound, Proposition 4.1 and Theorem 1.2. `orbitVNInput_of_finiteVNInput` formally reconstructs the required orbit transference from TV, retaining the same degree-only K. The universal-phase/supremum interface bridge TV-B remains unformalized.

## Derived OR — Mousavi orbit transference, now proved from TV

Primary: Hamed Mousavi, *Polynomial configurations and pointwise averages along Piatetski–Shapiro sequences*, [arXiv:2609.01847v1](https://arxiv.org/html/2609.01847v1), 1 September 2026.

Verified Proposition 1.4 and displayed (8), (10): for an invertible probability measure-preserving system, distinct-degree integer polynomials Q_i, B>0, |g|≤B on [M], and polynomial-phase correlations at most E, the L¹ norm of the orbit average is bounded by an implied polynomial-family constant times B(M⁻¹+B⁻¹E)^{1/K} times the product of the L∞ norms. Its proof uses L¹–L∞ duality, invariant orbit averaging over M^d translates, and Theorem 1.3, its quoted Teräväinen estimate.

The author subsequently supplied the complete LaTeX source, preserved unchanged at `manuscript/related-original/PSSequences.tex`, SHA-256 `a172126d8d75e2032dd9da685cc848f8f76967b2f69c84066d87c0815a5d6a6e`. Its compiled numbering confirms Proposition 1.4 (`p:orbit`) and equation (10); no version/date is printed in that supplied source.

The required real-weight, essentially 1-bounded interface is now proved as `orbitVNInput_of_finiteVNInput : FiniteVNInput → OrbitVNInput`. `OrbitPolynomials` proves translation by −1, degree preservation and a scale-independent spatial support constant. `OrbitMeasureHelpers` proves finite-average integrability, the explicit dual multiplier `conj(A)/‖A‖` (zero at A=0), its norm/pairing identities and integral invariance. `OrbitTransference` proves the exact cutoff identity at spatial length N^d and the integration argument. The original functions need only satisfy essential bounds: one conull set controls all their integer iterates. No independent theorem of this related paper remains an input to the prime project. This is the needed specialization, not a formalization of all conclusions of the related paper.

Depends into: p:pointwise-comparison, t:pointwise, and the revised c:long-variation.

## KM — KMTT

Primary: Ben Krause, Hamed Mousavi, Terence Tao, Joni Teräväinen, *Quantitative bounds for sets lacking polynomial progressions with shifted prime difference*, [arXiv:2608.19525v1](https://arxiv.org/html/2608.19525v1), 20 August 2026.

Verified locations and interfaces: Definition 2.2, (C,q)-coefficients; Lemma 5.1, (5.2), prime-mass truncation comparison; Proposition 5.2, hypotheses (5.9)–(5.11), conclusion (5.12), unweighted discrepancy at M₀∈[⌈M exp(−√log M)⌉,M]; (5.15), lower prime mass; Lemma 5.3, (5.25)–(5.28), weak regularity with a common modulus q^B and coordinate resolution M₀^{ν_i}; (5.35)–(5.36), enlarged divisibility parameters; (5.57)–(5.59), modulus and length recursions.

The manuscript p:KMTT is a composite consequence, not a directly quoted theorem. Its original mass-preserving local-factor density argument, length deduction, small-scale exclusion and literal coefficient-one normalization are now checked as `kmtt_density_increment_normalized`, under the separate external finite estimates. The main density theorem is not an input. The actual finite-support/real-form and exponent translations remain external bridges KM-U-B and KM-R-B.

Primary LaTeX source bytes were also downloaded from [arXiv source](https://arxiv.org/src/2608.19525v1) and inspected. Archive SHA256: `b7da309294a475b3fbfc8ff60ca39e3c42701fed0d40146a7dca560f2576ca45`; main source SHA256: `9d1cc58cabb0c80a883959548c9307f27d8b1ec2d8e056ef3ac9b88de3b61e6d`. Exact provisional transcription and line locations are retained in [KMTT_INPUTS_WORKING.md](KMTT_INPUTS_WORKING.md); whole downloaded source files remain intermediate files outside the distributable project.

**KM-J, separately identified:** (5.2) fixes a sufficiently small cutoff; no numerical cutoff is printed and no uniform fraction as that cutoff tends to zero is asserted. For the actual `KMTTCompatibleInput`, choose the fixed cutoff below the prior positive τmax, choose a smaller positive Lemma 5.1 discrepancy constant c₁ relative to its mass fraction, and rerun Proposition 5.2 with enlarged constants/thresholds, retaining (5.35)–(5.36). Two independent readings of the primary proof verified that its error budgets permit this selection. This is an unformalized source-proof reparameterization, **not** monotonicity of an already fixed theorem statement and **not** a conclusion from separate existential inputs. The actual type and its consumers are in [ASSUMPTIONS.md](ASSUMPTIONS.md). No compatible witness is supplied for every arbitrary parameter record.

A third-party search hit alleged a reanchoring error. Direct checking does not support its counterexample: Definition 2.2 requires the normalized leading coefficient at most C, excluding its proposed arbitrary leading coefficient M with fixed C. Do not propagate that allegation.

Depends into: p:KMTT, l:PS-discrepancy, t:szemeredi only.

## MW — Mirek–Wan–Wright

Primary: Mariusz Mirek, Renhui Wan, James Wright, *Pointwise convergence of polynomial multiple ergodic averages along the primes*, [arXiv:2505.15549v2](https://arxiv.org/html/2505.15549v2), 22 June 2026.

Verified Theorem 1.1(ii): von Mangoldt-weighted distinct-degree polynomial averages converge pointwise almost everywhere on a σ-finite measure-preserving system for inputs in finite L^{q_i}, with 1<q_i<∞ and Σ_i1/q_i≤1. The theorem permits integer polynomials with nonzero constant terms.

To apply it to this manuscript, use probability measure and L∞⊆L^{2ℓ} (ℓ≥1), so Σ_i1/(2ℓ)=1/2. Degree preservation under n↦n−1 is now proved in `OrbitPolynomials.lean`; the finite-Lp inclusion and complete source-theorem application remain bridge obligations. The exact published hypothesis is finite q_i, so an external interface stated directly for L∞ on a probability space is a specialization requiring these bridges. Weighted convergence is already the published conclusion; prime-power removal is not needed before invoking it.

Depends into: t:pointwise only.

## PNT — exact von Mangoldt mass normalization

Primary: Terence Tao, [246B Notes 4: The Riemann zeta function and the prime number theorem](https://terrytao.wordpress.com/2021/02/12/246b-notes-4-the-riemann-zeta-function-and-the-prime-number-theorem/), 12 February 2021, **Theorem 6 (Prime number theorem, von Mangoldt form)**.

Directly verified on the author's own page: x⁻¹Σ_{n≤x}Λ(n) tends to 1. This is the precise Chebyshev-psi formulation used in `PrimeNumberTheoremInput`. Restriction to integer cutoffs is included in the quoted specialization. No conversion from a different prime-counting normalization is being silently assumed. The elementary higher-prime-power residual and both actual cutoff unweighting applications are checked internally.

Depends into: Proposition 4.1, the ordinary and sparse mass limits, and Theorem 1.2.

## Optional no-Siegel footnote — not a required assumption

Primary: Ben Green, *On Landau–Siegel zeros*, [Hexagon:2610.00311v2](https://hexagonmath.org/2610.00311v2), source/PDF accessed from its record; Terence Tao, [19 October 2026 exposition](https://terrytao.wordpress.com/2026/10/19/a-sketch-of-the-proof-of-non-existence-of-siegel-zeroes/).

Green's Theorem 1.1 bounds Σ_{p≤q^C, χ(p)=−1}(log p)/p by (1/2+O(1/C))log(q^C)+O_C(1), for primitive nonprincipal real characters of sufficiently large conductor and sufficiently large even C. The text explicitly invokes an additional standard analytic argument to exclude Landau–Siegel zeros. An AP prime-mass lower bound still requires the PNT-in-progressions bridge with its ranges and constants. Tao's article is exposition, not a substitute for that bridge. The manuscript retains classical estimates (KMTT (5.2), (5.15)), so the formalization should not depend on this optional strengthening.

## Architecture safeguards

1. Exact Lean interfaces are printed from the implemented declarations in ASSUMPTIONS.md; this reference review is not itself a proof of them.
2. Verified citation means the external source states the indicated theorem. It does not mean the theorem has been formalized or independently proved here.
3. No mathematical axiom is needed: any external estimate can be an explicit theorem parameter or a field of a narrowly named hypothesis structure.
4. Keep external results, elementary specializations, and the current paper's original deductions separate in the statement map.

## Revision reference check — 2 November 2026

The revised manuscript uses MWW **Theorem 1.1(iv), equation (1.5)**, in the
same [v2 primary source](https://arxiv.org/html/2505.15549v2) already cited
for ordinary pointwise convergence. It gives r>2 variation estimates for
any λ-lacunary positive integer set, λ>1, in finite-Lq Hölder ranges. The
source defines the seminorm and full norm in (2.3)–(2.4); the full norm
estimate dominates the manuscript's seminorm. The specialization to
essentially bounded probability-space inputs is separately external
MW-V-B, not claimed as a consequence of the pointwise-only MW interface.

New endpoint background: LaVictoire, *Universally L1-bad arithmetic
sequences*, [arXiv:0905.3865v2](https://arxiv.org/pdf/0905.3865v2), Theorem
1.1 and Corollary 1.2, includes the primes; the journal bibliographic record
is J. Anal. Math. 113 (2011), 241–263. Mirek, [arXiv:1401.1361](https://arxiv.org/pdf/1401.1361),
page 4, discussion immediately after Theorem 1.14, explicitly raises the
endpoint problem for thin primes. These are background citations in a
remark, not additional Lean proof premises. No sparse-prime finite-Lp or
L1 endpoint claim is inferred from them. The optional Green/Tao footnote
is unchanged and unused.
