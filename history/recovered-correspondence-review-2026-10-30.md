# Recovered historical independent correspondence reviews

Recovered on 30 October 2026 by `/root/math_review` from that agent's own prior tool-call text and messages after the scratch reset. This records the mathematical findings of the earlier reviews, not a claim that the recovered project has already been rebuilt. The earlier general correspondence review in `correspondence-review.md` is preserved unchanged. Source hashes below identify the earlier reviewed versions; later recovery/build evidence is separate.

## Completed Proposition 2.3

Reviewed declarations: `ps_counting_comparison_gamma` and `ps_counting_comparison` in `FinalComparison.lean`, including their finite lifting, normalization, scale, and power-saving dependencies.

Conclusion of the prior independent review: `ps_counting_comparison` faithfully expresses manuscript Proposition 2.3, conditionally on the two displayed analytic inputs. No hidden strengthening of its hypotheses or weakening of its conclusion was found.

The degree d is fixed before cstar and ξ, and before the polynomial family, support constant, c, a, scales, modulus, and functions. C is chosen before a; the threshold on the floor scale is chosen after a and uniformly over Q and functions. This matches the source's a-independent implied constant and a-dependent sufficiently-large-M threshold. The eventual-in-N result legitimately implies the sufficiently-large-M result by the proved M≤N inequality.

The conclusion uses the actual integer rescaling, actual counting form with prime argument Qy+1, and actual discrepancy weight at γ=1/c. The parameter length is exactly floor((N/Q^(d−1))^(1/d)). Supports are the closed radius-C₀N interval; complex functions need not be nonnegative. The finite-support representation of f₀ exactly implements the unrestricted spatial sum. Signed polynomial coefficients and negative integer shifts remain allowed.

The exact double lift connects both summation variables, with normalization L^(d+1)/(NM). It is bounded above by Q² and below by Q²/2^d. Lifted supports use the fixed constant C₀2^d, so the finite VN constant does not acquire Q-dependence. Phase restriction, degree preservation, weight envelopes, and the Q² loss absorption are checked deductions. The exponent calculation uses t=1/K, s=min(1,σ), 8(1−γ)≤s*t, and eventual Q≤L^(s*t/8), leaving ξ=s*t/(4d)>0. The γ/c conversion uses cstar=1/(1−ε).

The external boundary remains SS's coefficient-uniform polynomial-phase bound and Teräväinen's fixed-family finite VN bound. The catalogue must distinguish the every-phase formulation from the published supremum statement and explain the degree-uniform K(d) interpretation of K≪_d1. The conditional deduction does not assume Proposition 2.3 or a substantially equivalent PS-prime comparison.

Reviewed historical hashes:

- FinalComparison.lean: `2fd2cd12a5785b11066d143057661632a514114a5860bcbf232bcc9d927b64c3`
- PowerSaving.lean: `6722ae033ea08a0b92efe5ef3162b9c728de0d47a96ba805e859499e0769e282`
- Comparison.lean: `d3de16b9fc7767e7c33ce0f6b84631ac863aaa43b8e696c1db433d4efd6c4a46`
- Lifting.lean: `df02851aff60df8218d7be5f7925654c1509de125d6c38b088413ce2188161b8`
- Scales.lean: `8a781bb888dd76ca131676b785bd8eba914f357652e67982205c27f99ca7d575`
- AsymptoticScales.lean: `69d7ab9ac1eb9468753b16a497d6ba48806c8fe00bde1a89c9387310d0fe3161`
- Asymptotics.lean: `2322d85f4e8ebb58465f62be1bd2fc6a4e54fd1021bde8fd279ad384e9ce2dce`
- ExceptionalTerms.lean: `b8e54529436a71a0892ef33a36a8688dc5cb0cb31e7da5c8a8868eaa1c2622d9`

## Conditional Theorem 1.2

Reviewed declaration: `PSPrimes.pointwiseErgodicTheorem_of_external_inputs` in `MainPointwise.lean`. Main source hash: `fac67a29e673f92efe61def28746ff6cbcf9d2ecb6f9b57a2d7ef0ba38be368b`.

Conclusion of the prior independent review: this declaration faithfully proves the full manuscript Theorem 1.2 conclusion under four explicit external hypotheses. No mathematical or statement-correspondence defect was found. This is independent of compilation and is not a claim that the external hypotheses are Lean-proved.

The nonempty family has positive strictly increasing degrees and zero constant terms. cstar is chosen before c, every probability space, action and observable, so its c-neighborhood is uniform over systems and functions. The maximum degree is derived from the actual last family entry. Universe polymorphism does not restrict X to finite, countable, standard-Borel or separable spaces.

The unfolded main specification includes a probability measure, an invertible measurable measure-preserving integer action, AEStronglyMeasurable complex functions, and a finite essential bound for each function. The theorem does not replace essential bounds with everywhere 1-bounds. Its homogeneity reduction divides by positive scalar bounds, proves essential orbit bounds simultaneously along all integer iterates using countability and measure preservation, and multiplies the common limit back by the finite product of scalars. Both positive and negative polynomial iterates are supported.

The conclusion has one function L and a common almost-everywhere set on which both actual selected averages converge to L. Selection predicates are the actual floor-power PS-primes and Nat.Prime. Orbit products evaluate P_i(n−1), with integer subtraction. Denominators are actual cardinalities in [1,N], and N runs through the full cutoff sequence. Finite zero-denominator conventions are explicit; infinitude and count divergence are derived internally from selected mass limits before unweighting.

The γ-neighborhood is shrunk to ensure γ>1/2. Actual prime/nonprime support decompositions and the elementary combined higher-prime-power mass estimate yield vanishing residuals. Applying the same argument to sample 1 derives selected mass limits, rather than assuming a PS-prime-count asymptotic. Positive monotone unweighting is applied only at primes p≥2. The equality 1/(1/c)=c is discharged. Discrete Abel summation, increasing enumeration, reindexing, full-cutoff interpolation and essential-bound homogeneity are deductions, not original-conclusion assumptions.

The four external premises are `ShaoSunPhaseInput`, `OrbitVNInput`, `PrimeNumberTheoremInput`, and `OrdinaryPrimePointwiseInput`. OR is an arbitrary-real-weight norm theorem and does not assume this paper's Dγ rate or pointwise comparison. MW is ordinary-prime weighted convergence and does not mention thin primes. Thus none assumes an original manuscript conclusion or equivalent reformulation. Their source-to-interface translations remain explicit external boundaries: direct polynomial-phase specialization; orbit supremum/shift/integrability specialization; finite-Lq-to-L∞ and shift specialization; ordinary PNT in the precise Mangoldt-mass formulation.

The pointwise theorem establishes its own cstar>1. Once the independent recurrence theorem has an admissible cstar, taking their minimum gives the manuscript's shared-cstar convention. This does not close the recurrence theorem.

Reviewed historical dependency hashes:

- Definitions.lean: `121d5bc25055fdfd72871c56069414d7b97305d0587f7c9cf7544585fa6f7298`
- OrbitInputs.lean: `c4a2958e44363f602c2df4275529f4ad8206c9413dafa96556f9a5ed1eb7d808`
- OrbitComparison.lean: `ba571d4ca7b13651f5c65eee1e174c0a72a3390784d759fd85a2f2ac2f9e0346`
- Representatives.lean: `59dbb774ae5907e7da677f7c2cf4567c8fc0162405eee89a4a7ea807cd67b669`
- Pointwise.lean: `965fc652b47f5480fbc0c85aa6882f7807806de7231acaf256f7f24c7ba3e308`
- PrimePowers.lean: `8fcb760ee7e424157cfee1c8b37130fd0043ad1eef849cfbbd56cd453a62ab9c`

The old review's earlier claims that the pointwise theorem was only a specification describe an earlier snapshot and are superseded by this recorded conditional completion, provided the recovered checked source and its dependencies are restored and rebuilt. The quantitative recurrence theorem remains a separate open obligation in that reviewed snapshot.
