# Manuscript-to-Lean map

The current authoritative source is the author's unedited revision supplied
on 2 November 2026, preserved as
[`manuscript/revised-2026-11-02/Draft.tex`](../manuscript/revised-2026-11-02/Draft.tex).
The earlier unchanged `manuscript/original/Draft1.tex` and its 14-page generated
PDF remain available. No independently supplied PDF accompanied either source.

The revision preserves all 48 earlier labels and adds `c:long-variation`: **49
labels, comprising ten labelled theorem-like statements and 39 equations**.
Its generated PDF has 15 pages. It also adds an unlabelled numbered endpoint Remark 1.3. This moves the quoted
Teräväinen theorem from 1.3 to 1.4; every other earlier statement and equation
keeps its number. The seven earlier deductions remain checked conditionally.
The new Corollary 4.2 also has a checked conditional proof, recorded below.
Two labelled statements quote external theorems; the endpoint remark is an
explicit expectation and background discussion, not a claimed theorem.

No manuscript conclusion is assumed to establish another conclusion. External
theorems and source-to-interface translations are catalogued in
[ASSUMPTIONS.md](ASSUMPTIONS.md). The previous map is retained in
[history](../history/pre-revision-2026-11-02/docs/PAPER_MAP.md).

“Checked” refers to the indicated implementation and its module compilation.
It does not assert that an external hypothesis has been proved. The final
clean-build and axiom-audit outcomes are recorded separately in `evidence/`;
this map is not a substitute for those command logs.

## Numbered statements

| Manuscript | Original label | Checked declaration / external interface | Scope and dependencies |
|---|---|---|---|
| Theorem 1.1 | `t:szemeredi` | `quantitative_recurrence` in `MainRecurrence.lean` | **Conditional checked:** `ShaoSunPhaseInput`, `FiniteVNInput`, `KMTTRegularityInput`, `KMTTCompatibleInput`. Actual finite sets and PS primes; c* and κ precede c, and N₀(c) precedes N and A. The original iteration is constructed. |
| Theorem 1.2 | `t:pointwise` | `pointwiseErgodicTheorem_of_external_inputs` | **Conditional checked:** SS, `FiniteVNInput`, `PrimeNumberTheoremInput`, `OrdinaryPrimePointwiseInput`. The orbit estimate is proved from finite VN; no own-paper result is an independent input. Actual count-normalized averages, probability systems, essential L∞ bounds, and one common a.e. limit. |
| Remark 1.3 | unlabelled | No Lean theorem | Conjectural finite-Lp extension and endpoint background; not an assertion proved by this development. |
| Theorem 1.4 (previously 1.3) | `t:teravainen` | `FiniteVNInput` | **Quoted external:** fixed-family finite generalized von Neumann estimate. Positive-degree specialization and the supremum-to-every-phase interface are explicit external translations. |
| Theorem 2.1 | `t:shao-sun` | `ShaoSunPhaseInput` | **Quoted external:** coefficient-uniform polynomial-phase consequence of Shao–Sun. The circle/binomial nilsequence specialization is explained but not formalized. |
| Lemma 2.2 | `l:progression-phase` | `progressionPhase_of_shaoSun` | **Conditional checked on SS:** exact character projection, progression reindexing, n=1 cancellation, and QM+1 endpoint absorption. The saving is chosen before γ. |
| Proposition 2.3 | `p:comparison` | `ps_counting_comparison` | **Conditional checked on SS and finite VN:** degree-only c* and saving; the bound constant precedes a, while the large-M threshold may depend on a. The original floor scale, support, and normalization are retained. |
| Proposition 3.1 | `p:KMTT` | `kmtt_density_increment_normalized` | **Conditional checked on `KMTTUnweightedInput` and `KMTTRegularityInput`:** the original local-factor deduction, small-scale exclusion, divisibility, actual progression, and literal coefficient-one length bound are proved. The useful prefactor version is `kmtt_density_increment`. |
| Lemma 3.2 | `l:PS-discrepancy` | `ps_prime_discrepancy` | **Conditional checked on SS, finite VN, and `PrimeProgressionMassWitness` for the same comparison parameters:** actual forbidden configurations, collisions, prime powers, model overlap, and uniform error absorption. `KMTTCompatibleInput` supplies compatible data in Theorem 1.1. |
| Proposition 4.1 | `p:pointwise-comparison` | `ps_orbit_comparison` | **Conditional checked on SS, finite VN, and PNT:** the L1 power saving, summable-subsequence passage, and full-sequence a.e. comparison are proved. MW is needed only for the subsequent common-limit theorem. |
| Corollary 4.2 | `c:long-variation` | `lacunary_variation_of_external_inputs` in `LongVariation.lean` (**conditional checked**) | SS, finite VN, and the newly documented `OrdinaryPrimeVariationInput` (MW-V). Infinite r-variation of actual weighted sparse averages; r>2, λ>1; c* before r, λ, with the norm bound uniform over positive λ-lacunary sequences and systems. No PNT or ordinary pointwise-convergence premise is required. |

## Definitions and numbered equations

Routine supporting lemmas are grouped with the mathematical step they serve.
The every-phase `PhaseBound` interface replaces a literal supremum object;
its published-supremum translation remains explicit in the external catalogue.

| Number | Original label | Implementation and verified scope |
|---|---|---|
| (1) | `e:polynomials` | `PolynomialFamily`: nonempty integer family, all zero constant terms, all positive degrees, and strictly increasing degrees. P₀=0 is supplied by `pattern` / `recurrencePolynomials`, rather than counted as a positive-degree family member. |
| (2) | `e:pattern` | `pattern`, `ContainsConfiguration`: actual PS prime p, integer argument p−1, all ℓ+1 entries in A, and injectivity for pairwise distinctness. No upper bound on p is added. |
| (3) | `e:PS-average` | `selectedAverage (IsPSPrime c)` on `orbitProduct`. `selected_infinite_of_mass_limit`, `selected_count_tendsto_atTop`, and the main theorem establish count divergence; the finite zero-denominator convention is harmless. |
| (4) | `e:prime-average` | `selectedAverage Nat.Prime` on the same orbit product. `selected_primes_unweighting` and the main theorem give the actual ordinary-prime average and the common limit. |
| (5) | `e:weights` | `sparseMangoldt`, `discrepancyWeight`, with Mathlib's actual von Mangoldt function; prime values, nonnegativity, and cancellation at 1 are proved. Positive natural weight indices and the finite-sum domains implement the required zero extension. |
| (6) | `e:u-norm` | `complexPhase`, `phaseSum`, `PhaseBound`: every real polynomial of the required degree is tested without coefficient restrictions. The relation to the published supremum notation is an external interface translation, not an additional proved supremum theorem. |
| (7) | `e:teravainen` | `polynomialForm`, `FiniteVNInput`; exact M⁻(d+1) normalization, genuine spatial support, and boundedness hypotheses. The deep estimate is external. |
| (8) | `e:scaled-vn` | `homogeneous_polynomialForm_bound`: checked homogeneity from a fixed-family finite-VN instance, with the positive magnitude B and phase normalization explicit. |
| (9) | `e:rescaled-polynomial` | `rescale`, `eval_rescale_mul`, `eval_rescale_ediv`: the integer polynomial is constructed coefficientwise; Q·P_Q(y)=P(Qy) proves the displayed quotient is exact. |
| (10) | `e:shao-sun` | `ShaoSunPhaseInput`: external arithmetic estimate, with ε and σ before γ, then the bound constant before the cutoff and all phase coefficients. |
| (11) | `e:progression-phase` | `progressionPhase_of_shaoSun`: the complete required every-phase progression estimate, conditional only on SS. |
| (12) | `e:counting-form` | `countingForm`: the finitely supported f₀ implements the unrestricted integer x-sum exactly; the other factors and NM normalization are unchanged. |
| (13) | `e:comparison` | `ps_counting_comparison`: complete N⁻ξ estimate with the manuscript's parameter order and uniformity. |
| (14) | `e:lifting-scales` | `floorScale_power_bounds`, `liftedScale_power_bounds`, `liftedScale_normalization_identity`, `liftedScale_normalization_bounds`; `AsymptoticScales` proves the eventual positive-scale and subpower-modulus applications. |
| (15) | `e:lift-identity` | `liftFunction_rescale`, `lifting_sum`, `countingForm_lift`: exact spatial and parameter reindexing, including the Q² normalization cost. |
| (16) | `e:theta-u` | `phaseSum_liftWeight`, `PhaseBound.liftWeight`: exact finite-sum identity and the required correlation bound without coefficient restrictions. Magnitude and saving are discharged in `Comparison` and `PowerSaving`; no separate supremum-equality declaration is claimed. |
| (17) | `e:rescaled-coefficients` | `coeff_rescale`, `natDegree_rescale`, `rescale_coeff_bound`, `rescale_hasCQCoefficients`: one original coefficient bound works for every positive modulus. |
| (18) | `e:prime-discrepancy` | The precise premise of `KMTTDensityIncrementWitness`; `ps_prime_discrepancy` establishes it from actual absence. `realSetCount_eq_setCountingForm` and the model identities prove the real/complex and support translations. |
| (19) | `e:density-increment` | `dense_progression_of_local_discrepancy`, `DensityIncrementResult`, `kmtt_density_increment_normalized`: an actual AP inside [N], with its actual intersection cardinality and positive increment. |
| (20) | `e:increment-length` | `regularity_resolution_lower`, `truncated_scale_power_lower`, `KMTTDensityIncrementWitness.normalize_length`: smallest-degree scale, largest-degree exponential loss, and literal coefficient-one estimate. Increasing K₁ restricts admissibility and absorbs the positive prefactor by one extra inverse modulus power. |
| (21) | `e:m0` | `KMTTUnweightedWitness`, the external KMTT Proposition 5.2 interface, supplies an integer M₀ with the stated truncation bounds. Positivity and application to regularity are proved in `kmtt_density_increment_of_witnesses`. |
| (22) | `e:unweighteddisc` | The same external witness supplies the actual unweighted discrepancy ≥c₁δ^(ℓ+1)/4. Its conversion into a denser progression is proved, rather than assumed. |
| (23) | `e:resbound` | `KMTTRegularityWitness.regularity` quotes source coordinate-dependent AP resolution. `regularity_resolution_lower` proves the minimum-degree bound and retains all positive prefactors. |
| (24) | `e:localfactorforms` | `realConfigurationForm_sub_model`, `regularity_retains_discrepancy`, `localFactorDifference_bound`, `density_increment_from_local_discrepancy`: checked approximation retention, equal mass, product telescope, and dense-atom extraction. |
| (25) | `e:forbidencond` | `NoRescaledConfiguration`: exact actual PS-prime condition Qy+1 with all ℓ+1 entries distinct. `ConfigurationTransport` proves initial and successive affine preservation. |
| (26) | `e:model-lower` | `abs_eval_rescale_le_tenth_floorScale`, `card_translatedIntervalIntersection_ge_half`, `modelCountingForm_lower_of_primeMassWitness`: coefficient control and interval overlap are proved; fixed-cutoff classical mass is external. The compatible witness retains the same c₁. |
| (27) | `e:comparisonterms` | `countingForm_discrepancy`, `comparison_on_sets`, `ordinary_setCountingForm_le_error`: exact sign and linearity plus the complete Proposition 2.3 error. |
| (28) | `e:collisionterms` | `card_rescaled_collisions_le`, `card_badParameters_le`, `sparse_setCountingForm_le_exceptional`: at most d·choose(ℓ+1,2) collision parameters and their actual weighted contribution. `eventually_sparseCountError_power_bound` proves uniform power decay. |
| (29) | `e:prime-powers` | `card_higherPrimePowers_le`, `higherPrimePowers_mangoldt_mass_le`, `higherPrimePowers_combined_mass_rpow_le`: elementary prime-power count and mass. An injective map bounds the progression by the actual global exceptional set; `DiscrepancySaving` proves the uniform N-saving. |
| (30) | `e:prime-mass` | `PrimeProgressionMassWitness.full_mass` quotes classical KMTT (5.15) in the exact admissible range. `eventually_powerSaving_le_density_mass` proves uniform error domination. The optional no-Siegel footnote is unused. |
| (31) | `e:initial-scale` | `exists_initial_residue`, `initialResidueLength_half_lower`, `initial_modulus_log_bound`, `eventually_initial_modulus_half`: dense full residue-class pullback, actual floor length, and N/(2Q₀) lower bound. |
| (32) | `e:next-modulus` | `RecurrenceStep.modulus_update`, `recurrenceState_next_of_increment`, `NoRescaledConfiguration.progression_pullback`: Q_{j+1}=Q_j^(b_j+1), actual affine set update, and exact prime-parameter transport. |
| (33) | `e:modulus-control` | `finite_iteration_bounds`, `horizon_growth_bound`, `initial_modulus_log_bound`: derives the α-power bound for actual past modulus updates over the density-dependent horizon. |
| (34) | `e:length-recursion` | `log_increment_length_lower_bound_initial_density`: derives the uniform logarithmic recursion from the actual finite length, retaining its positive prefactor and all losses. |
| (35) | `e:length-control` | `finite_iteration_bounds`, `quantitative_prefix_admissibility`, `quantitative_recurrence_from_steps`: accumulated bounds imply every current numerical condition from already constructed prefixes; the final theorem supplies actual increments. |
| (36) | `e:weighted-averages` | `weightedAverage` on positive indices and `orbitProduct`; `weightedAverage_eq_weightedMean_shift` proves the bridge to the generic range-indexed lemmas. |
| (37) | `e:weight-mass` | `PhaseBound.mass`, `discrepancy_mass_tendsto`, `sparse_mass_tendsto_of_phase`: zero phase plus the external ψ-form PNT gives the actual sparse weighted mass limit. |
| (38) | `e:L1-comparison` | `discrepancy_orbit_L1_power_bound`, `ps_orbit_discrepancy_L1_gamma`: actual L1 saving from SS and the orbit estimate derived from finite VN, with envelope and exponent absorption proved. No independent L1-decay assumption is used in the final application. |
| (39) | `e:primepowers` | `higherPrimePowers_combined_mass_rpow_le`, `higherPrimePowers_combined_mass_div_tendsto_zero`, `nonprimeWeightedMean_tendsto_zero`: elementary O(N^(3/2−γ)log²N) and o(N) removal for γ>1/2, applied to both actual weights. |

## Substantial unnumbered arguments

| Mathematical argument | Current implementation and boundary |
|---|---|
| Actual PS set and introductory sparsity | `IsPS` and `IsPSPrime` use the floor-power sequence and actual primality. The introductory PS-prime counting asymptotic is background literature, not a formalized theorem or an extra input used by either main proof. The count divergence needed for the averages is proved from the recorded mass inputs. |
| Nilsequence specialization and coefficient uniformity | The circle filtration and binomial expansion explain SS. This translation remains external; no nilmanifold formalization or coefficient-bound replacement is claimed. |
| Fourier restriction and endpoints | `Progressions` proves character orthogonality, exact reindexing, phase degree control, Dγ(1)=0, and QM+1 absorption, including Q=M=1. |
| Fixed-family lift and support | `Lifting` and `Scales` prove both reindexings, divisibility, support dilation, phase composition, and normalization. VN is applied only to the fixed original polynomials; coefficient-uniform VN is not assumed. |
| Envelope and subpower absorption | `ExceptionalTerms`, `PowerSaving`, `AsymptoticScales`, and `FinalComparison` establish magnitude, logarithmic absorption, modulus loss, exact floor-scale transfer, and complete uniform Proposition 2.3. |
| Classical source compatibility | `KMTTCompatibleInput` selects the same p for unweighted discrepancy and fixed-cutoff mass. The source-level joint selection is external KM-J; unrelated existential witnesses are not combined. |
| Regularity application and local argument | `SmallScale` excludes the source alternative uniformly; `regularity_divisibility` proves the lcm requirement; `Density` and `DensityIncrement` prove equal mass, telescoping, dense-atom extraction, its AP realization, and inherited length. |
| Literal length normalization | `KMTTNormalization` and `NormalizedDensityIncrement` prove that enlarging K₁ restricts admissibility, preserves comparison/mass witnesses, and absorbs the positive length prefactor by replacing Aq with Aq+1. This bridge is checked. |
| Absence implies sparse error only | `PrimeDiscrepancy` proves actual PS-prime terms outside the collision set vanish. Roots bound collisions; injectivity controls higher prime powers. `DiscrepancySaving` and `FinalPrimeDiscrepancy` discharge all eventual error inequalities uniformly in Q,s,δ,A. |
| Smooth modulus and full-fiber initialization | `SmoothModuli` proves lcm positivity, factorial/log bounds, smoothness, and power preservation. `InitialProgression` proves weighted pigeonhole using full residue intersections with their actual possibly different lengths. |
| Actual iteration and contradiction | `RecurrenceState`, `RecurrenceStep`, and finite `RecurrencePrefix` retain actual sets and forbidden configurations. `FiniteIterationBounds` derives estimates from past steps; `MainRecurrence` constructs every next stage and contradicts density≤1 at the exact finite horizon. κ precedes c. |
| Finite-to-orbit transference | `orbitVNInput_of_finiteVNInput` proves the required real-weight specialization of the related manuscript's Proposition 1.4 from finite VN. Exact shifted degrees, fixed spatial support, N^d normalization, explicit complex duality, integrability and invariant averaging are checked. `OrbitVNInput` is a derived specification, not an independent external input. |
| Tonelli and full-sequence interpolation | `ae_tendsto_zero_of_summable_integral_norm`, `polynomialCutoff_summable_decay`, and `ae_weightedAverage_comparison_of_L1_decay` prove the subsequence and bracketing argument. `OrbitComparison` supplies actual nonnegative masses and their limits. Integer polynomial subsequences suffice in place of real-power floors. |
| Prime powers, positive counts, and Abel summation | `PrimePowers`, exact decompositions in `Pointwise`, and `MainPointwise` remove the actual residuals. `selectedAverage_tendsto_of_weighted_limits` proves cutoff/enumeration and discrete Abel for the actual selected sets, including count divergence and eventual positivity. No continuous partial-summation bridge is assumed. |
| Essential bounds and common limit | `Representatives` constructs bounded representatives and proves orbitwise a.e. agreement over all integer iterates. `pointwiseConclusion_of_oneBounded` restores arbitrary complex essential L∞ bounds. `MainPointwise` proves one common limit for both actual normalized averages from external ordinary weighted convergence. |

## Reading the main results

`quantitative_recurrence` proves the exact `QuantitativeRecurrence` specification:
c* and κ are uniform in c, N₀ may depend on the fixed family and c, and the
conclusion includes every original support, primality, and distinctness condition.
Negative coefficients and negative polynomial values are allowed.

`pointwiseErgodicTheorem_of_external_inputs` proves the exact
`PointwiseErgodicTheorem` specification: an invertible probability-preserving
integer action, complex measurable functions with essential bounds, actual
PS-prime and ordinary-prime cardinality denominators, and one common a.e.
limit. Its four external premises are SS, finite VN, PNT and ordinary-prime weighted convergence; the required own-paper orbit argument is proved internally. It does not strengthen essential bounds to everywhere bounds in the
final statement or restrict to finite systems.

The seven earlier conditional statements contain no remaining open original
proof obligation. The revision adds Corollary 4.2; its implementation/build
status is recorded above and in the revision notes. The two quoted statements and the listed external translations
remain unformalized. Standard foundational axiom lists certify neither those
analytic inputs nor manuscript correspondence; the assumption catalogue and
mathematical reviews address these separate questions; no independent human expert review is claimed.

## Changes introduced in the 2 November revision

The primary addition is the infinite lacunary r-variation seminorm and
Corollary 4.2. Its proof uses the already checked all-N L1 power saving, a
uniform geometric series bound, the variation triangle inequality, and the
MWW variational estimate. This requires the extra MW-V input; the existing
MW pointwise-convergence interface alone does not assert a variation bound.

The endpoint Remark 1.3 makes an expectation explicit and cites counterexample
background. The introductory relative-density discussion, revised literature
review, and shorter prime-power exposition do not change the hypotheses or
conclusions of the two main theorems. The cited optional no-Siegel observation
remains unused. See [REVISION_2026_11_02.md](REVISION_2026_11_02.md) for proof
architecture and exact source/correction notes.

The new `variationChain_eq_ofReal` theorem identifies every finite-chain
ENNReal expression with the nonnegative real formula printed in the paper.
`rVariation` then takes the genuine countable infinite supremum. The output
uses a nonnegative extended integral and the exact `eLpNorm f ∞ μ` product,
so neither divergent variation nor zero essential norms are hidden by a
real-integral convention.
