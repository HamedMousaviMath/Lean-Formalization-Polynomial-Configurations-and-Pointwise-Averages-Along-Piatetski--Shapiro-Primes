# KMTT source interfaces — provisional working transcription

This document records primary-source mathematical facts for designing external theorem parameters. It does not introduce Lean axioms, instantiate any input, or claim that the manuscript's Proposition 3.1 has been proved. Explicit interfaces require review against the resulting Lean types. The source uses `k` for the total number of functions; in the supplied manuscript `k = ℓ + 1`.

Primary source: B. Krause, H. Mousavi, T. Tao and J. Teräväinen, *Quantitative bounds for sets lacking polynomial progressions with shifted prime difference*, arXiv:2608.19525v1, 20 August 2026. [HTML](https://arxiv.org/html/2608.19525v1), [source archive](https://arxiv.org/src/2608.19525v1), [PDF](https://arxiv.org/pdf/2608.19525v1). The actual LaTeX source was downloaded and read on 30 October 2026. Intermediate source files are outside the project, at `../reference-work/Main__17_.tex` and `../reference-work/refs.bib`. Source archive SHA256: `b7da309294a475b3fbfc8ff60ca39e3c42701fed0d40146a7dca560f2576ca45`; main LaTeX SHA256: `9d1cc58cabb0c80a883959548c9307f27d8b1ec2d8e056ef3ac9b88de3b61e6d`. These are provenance checks, not mathematical verification.

## Conventions that every interface must retain

- `[X] = {1,…,floor X}`. For natural `M>0`, `E_{y≤M}` divides by `M`. Spatial sums run over all integers, not only `[N]`.
- `L(s)=lcm(1,…,s)` for integer `s≥2`; `P⁺(1)=1`.
- Definition 2.2: an integer polynomial `P(y)=a_e y^e+…+a_1y`, with `e≥1`, has `(C,q)` coefficients precisely when `P(0)=0`, `a_e=a'_e q^(e−1)` for an integer `a'_e` with `0<|a'_e|≤C`, and `|a_j|≤C|a_e|` for `1≤j<e`. The normalized leading coefficient requirement is essential.
- Equation (3.4), source lines 985–996: for `P_0=0`,
  `T_{N,M,w,q}(f_0,…,f_{k−1}) = (N M)^−1 Σ_{x∈Z} Σ_{y=1}^M w(qy+1) ∏_{i=0}^{k−1}f_i(x+P_i(y))`.
  The `P_i` here are the actual input polynomials. The source operator does not silently rescale them.
- Section 3.3, source lines 998–1025: a local factor is a partition of all `[N]`. Projection is the mean of `f` on its atom, extended by zero outside `[N]`. A local factor of resolution `S` and modulus `h` has atoms that are nonempty arithmetic progressions of common difference `h` with cardinality between `S` and `2S`. Thus resolution means cardinality, not diameter; every atom is `(h Z+a) ∩ I` for an interval `I`.

## Parameter design for Proposition 5.2

Source lines 3124–3171, equations (5.6)–(5.8). Fix integers `d,k` with `k≥2`, real `C≥1`, and choose `c₁=c₁(C,d,k)∈(0,1]` supplied by Lemma 5.1. Existence of a distinct positive-degree family already implies `d≥1` and `k−1≤d`. The source does not claim Proposition 5.2 for an arbitrary user-specified `c₁`.

Put `𝒞=2+dC²`. Let `s=s(d,k)` come from Proposition 3.3 and `t=t(s,d)>0` from Lemma 4.4. Put `η₀=min(2^(−s),t)>0`. The absolute prime-uniformity parameter satisfies `0<c₀<1/11`; set `α_{d,k}=c₀ c_s/2` with `0<c_s≤1` from Lemma 3.1. Choose `c'=c'(d,k)>0` so that

`0 < 10c' < min(α_{d,k}/100,1/10)` .  (5.7)

Choose `Cbold=Cbold(C,d,k)` and `Kbold=Kbold(C,d,k)≥2` large enough that

`200/Cbold<c'`, `Cbold η₀≥100k`, and `Kbold^(−η₀/10)≤2^(−4k−50)c₁`.  (5.8)

The source explicitly permits enlarging these constants. Its subscripts `d,k` on `Cbold,Kbold` do not remove the stated dependence on `C`. After Lemma 5.3 it enlarges them further:

`Cbold≥3kA'`, `Kbold≥(16/c₁)^A'+1`.  (5.35)

Consequently, for every `0<δ≤1`,

`ceil(((c₁/16) δ^(3k))^(−A')) ≤ ceil(Kbold δ^(−Cbold))`.  (5.36)

These constants are chosen before the varying scale, density, modulus, polynomial family and set. A Lean catalogue should package compatible constants once. It should not choose new constants after seeing the density-increment atom.

## Proposition 5.2: weighted discrepancy to unweighted discrepancy

Source label `lem:chaining`, lines 3173–3239; equations (5.9)–(5.12).

For the fixed parameters and constants above there is a sufficiently large threshold `N₀(C,d,k)` so that all the following hold uniformly. Let integers `N≥N₀`, `q≥1`, `σ≥2` and real `δ` satisfy

1. `(log N)^(−1/Cbold²) < δ ≤ 1`;
2. `ceil(Kbold δ^(−Cbold)) ≤ σ ≤ (log N)^c'`;
3. `q ≤ exp((log N)^(2c'))`, `P⁺(q)≤σ`, and `L(σ)|q`.

Set

`M=floor((N/q^(d−1))^(1/d))`,

`Mmin=ceil(M exp(−sqrt(log M)))`.

Let `P_1,…,P_{k−1}∈Z[y]` have `(C,q)` coefficients with

`1≤deg P_1<⋯<deg P_{k−1}=d`.

Let `A⊂[N]`, `|A|=δN`. If

`|T_{N,M,Λ,q}(1_A,…,1_A) − T_{N,M,Λ,q}(δ1_[N],…,δ1_[N])| ≥ c₁ δ^k E_{y≤M}Λ(qy+1)`,

then some integer `M₀` satisfies `Mmin≤M₀≤M` and

`|T_{N,M₀,1,q}(1_A,…,1_A) − T_{N,M₀,1,q}(δ1_[N],…,δ1_[N])| ≥ c₁ δ^k/4`.

The supplied paper's Proposition 3.1 must still deduce a dense progression from this result and weak regularity; that dense progression is not part of this input. The source theorem is specifically for indicators and their constant-density model, not an arbitrary pair of tuples.

## Lemma 5.3: weak regularity with coordinate-dependent resolutions

Source label `cl:short-scale-regularization`, lines 3873–3918; equations (5.25)–(5.28). Fix `C,d,k` as above. There exists `A'>0`, depending only on `C,d,k`. For integers `N,q≥1`, real `0<ε<1/2`, suppose

`L(ceil(ε^(−A')))|q`.  (5.25)

Let the `P_i` have the same coefficient and degree conditions. Define

`ν₀=deg P_1`, and `ν_i=deg P_i` for `1≤i≤k−1`.

In particular, **ν₀ is the smallest positive degree, not deg(P₀)=0**. Let integer `M₀` satisfy

`1≤M₀≤(N/q^(d−1))^(1/d)`.

Let `f_0,…,f_{k−1}:Z→C` be 1-bounded and supported in `[N]`. Then one of the following alternatives holds:

- Small scale: `M₀ ≪_{C,d,k} (q/ε)^{O_{d,k}(1)}`.  (5.26)
- Regular approximation: there are local factors `B_i` of `[N]`, all with common modulus `q^B` for an integer `1≤B=O_d(1)`, such that
  `|T_{N,M₀,1,q}(f_0,…,f_{k−1}) − T_{N,M₀,1,q}(Π_{B_0}f_0,…,Π_{B_{k−1}}f_{k−1})| ≤ ε`  (5.27),
  and the resolution in coordinate `i` is at least
  `q^{−O_{d,k}(1)} ε^{O_{d,k}(1)} M₀^{ν_i}`.  (5.28)

The statement has **no sufficiently-large-N hypothesis**, no smoothness hypothesis on `q`, and no density `δ`. Its small-scale alternative must be retained; excluding it is an original quantitative deduction in the supplied manuscript. The resolution lower bound has an implicit positive prefactor depending on the fixed parameters, as made explicit by the proof below.

A usable expanded constant interface is: choose positive constants `A',Csmall,Asmall,cres,Ares` and integer `Bmax≥1` before all varying data. The small bound can be written `M₀≤Csmall(q/ε)^Asmall`; the regular branch has some `1≤B≤Bmax` and integer resolutions `S_i≥1` with `S_i≥cres q^(−Ares) ε^Ares M₀^ν_i`. Allowing all constants to depend on `C,d,k` is weaker than the sharper exponent dependence printed in the source; this relaxation must be stated if adopted. The factors themselves, `B` and resolutions can depend on all varying data. This is a proposed unpacking of the mathematical O-notation, not an already checked Lean declaration.

### What the proof actually constructs

Source lines 3920–4080. The local inverse input supplies correlation and Lipschitz control on progressions of step `q' q^b`, with `q'≪_{C,d,k}ρ^{−O_{d,k}(1)}`, `b=O_d(1)`. To handle coordinate zero, reanchor by `x'=x+P_1(y)` and use the shifted system `−P_1,P_2−P_1,…,P_{k−1}−P_1`, whose coefficient parameter is `2C²`. This is why `ν₀=deg P_1`.

Apply at `ρ=ε/(2k)`. Choose `A'` so all relevant auxiliary `q'≤ceil(ε^(−A'))`; divisibility (5.25) gives `q'|q`. Choose `B=O_d(1)` exceeding every possible `b+1`; then `q'q^b|q^B`. The source proof chooses this bound uniformly; its printed conclusion only needs an existential common `B` in the regular branch.

For a sufficiently large `C₂=O_{d,k}(1)` and sufficiently small `c₂=c₂(C,d,k)∈(0,1/4]`, the construction uses

`S_i=max(1,floor(c₂ q^(−C₂) ε^C₂ M₀^ν_i))`.

The constants satisfy `C₂≥2A+B` and `C₂+d−1≥B` for the inverse exponent `A`. Each residue class modulo `q^B` is partitioned into consecutive blocks of `S_i` points, merging a short final block into its predecessor; if `S_i=1`, singleton atoms suffice. When `S_i≥2`, the proof establishes `S_i≤N/(4q^B)`, so the construction has enough points. Every atom has between `S_i` and `2S_i` points, and

`S_i≥(c₂/2)q^(−C₂)ε^C₂M₀^ν_i`.

The factors are chosen before testing a telescoping residual. If approximation fails, a residual correlates with a function nearly constant on every atom; its atomwise mean zero gives a contradiction. No density-increment conclusion is assumed.

## Lemma 5.1 and prime-mass estimates needed by the discrepancy branch

Source label `lem:full-set-discrepancy`, lines 2997–3122. It fixes `d,k` with `k≥2`, `C≥1`, sufficiently large `N`, and assumes

`exp(−(log N)^(1/100))<δ≤1`, `q≤w_*(N)=ceil(exp((log N)^c₀))`, `0<c₀<1/11`.

For `M=floor((N/q^(d−1))^(1/d))`, the same polynomial hypotheses and `A⊂[N]` of size `δN`, absence of every pairwise-distinct configuration with **ordinary** prime `qy+1` yields discrepancy at least `c₁ δ^k EΛ(qy+1)`. This entire absence theorem cannot replace the supplied paper's sparse-prime Lemma 3.2: its absence hypothesis differs. Only the separately recorded prime-mass facts below should be quoted for that argument.

### Initial-mass comparison (5.2)

Source label `e:initial-prime-mass`, lines 3026–3090. The proof chooses a sufficiently small fixed `κ=κ(C,d,k)>0` so that for `Mκ=floor(κM)` every `1≤y≤Mκ` has `max_i|P_i(y)|≤N/10`. It proves

`Σ_{y≤Mκ}Λ(qy+1) ≫_{C,d,k} κ Σ_{y≤M}Λ(qy+1)`.

The selected `κ` and the positive comparison constant are chosen before `N,q` and the varying polynomial family. This is not a statement uniform in every variable `κ∈(0,1)`. A general fixed-κ version could be extracted from the proof with constants and threshold depending on κ, but that extension must be identified separately if used.

The analytic input is source Lemma 2.1, equation (2.5): for fixed `A≥1`, sufficiently large `N`, `q≤w_*(N)`, and integer `T` with `N^(1/A)≤qT≤N^A`, the normalized progression mass is

`q/φ(q) · (1 − ((qT+1)^(β−1)/β) 1_{qSiegel|q}) + O_A(exp(−c_A sqrt(log N)))`,

uniformly in `q,T`. The exceptional term is omitted if absent, and uses the single conductor/zero defined at scale `N`. The proof of (5.2) applies this at both `T=M` and `T=Mκ`, compares their exceptional factors, and uses an effective lower bound for `1−β`. No no-Siegel assumption is made.

### Full progression mass (5.15)

Source label `e:lowvonm`, lines 3295–3348. Under the Proposition 5.2 scale assumptions, in particular `q≤exp((log N)^(2c'))` and `M=floor((N/q^(d−1))^(1/d))`, the source proves

`E_{y≤M}Λ(qy+1) ≫ exp(−O((log N)^(2c'))) >0`.

A safe quantified input uses fixed positive constants `b_mass,B_mass` and a threshold depending on the fixed parameters, with

`EΛ(qy+1) ≥ b_mass exp(−B_mass(log N)^(2c'))`.

Do not replace this by `EΛ~q/φ(q)` uniformly: the retained exceptional-zero factor can be small. The source proof uses (2.5) with `A=2d` and the effective estimate `1−β≫qSiegel^−1≥q^−1`. It is independent of the set `A` and of any absence hypothesis.

## Remaining original deductions

To derive the supplied manuscript's Proposition 3.1, Lean must still specialize the two external inputs to `k=ℓ+1`, establish compatible constants and divisibility, eliminate the small-scale alternative, interpret actual progression atoms, prove the equal-mass and telescoping contradiction, and obtain the stated length bound. The recurrence iteration and its uniform admissibility are further obligations. For Lemma 3.2, one must combine finite comparison, sparse-prime absence, collisions and higher prime powers with the actual two prime-mass bounds above. Quoting source Lemma 5.1 wholesale would not discharge that sparse-prime argument.

## KM-J: joint constant-selection bridge (explicitly external)

The finite discrepancy lemma now takes `PrimeProgressionMassWitness p d τmax` for **the same** `p : KMTTComparisonParameters ℓ Adiv` used in the unweighted comparison. Separate existence of some `p` from `KMTTUnweightedInput` does not produce this compatible witness. No mass witness is asserted for every arbitrary parameter record.

For the application, `τmax=1/(10*C*(d+1))` is fixed from the coefficient bound, before the varying scale, density and modulus. The primary source does **not** print an explicit value of its initial κ, so the claim that its already selected κ automatically satisfies this τmax is not justified. The following proof-level reparameterization supports a joint existential external interface:

1. In source Lemma 5.1, choose the fixed sufficiently small κ additionally at most τmax. The argument proving (5.2), including its floor comparison and exceptional-zero factor comparison, works with this fixed smaller positive κ. Its constants and sufficiently-large-N threshold may depend on κ. This is not a uniform assertion as κ tends to zero.
2. Let r>0 be the resulting fixed lower bound for `sum_{y≤floor(κM)} Λ(qy+1) / sum_{y≤M} Λ(qy+1)` on the source scale range. Choose the Lemma 5.1 discrepancy constant `c₁` no larger than `r/4`, no larger than 1, and no larger than a valid constant in that lemma. The model lower bound (5.4) is at least `(r/2) δ^k` times the full mass; the negligible collision and higher-prime-power contribution can be absorbed leaving this smaller `c₁`.
3. Rerun the source proof of Proposition 5.2 with this **fixed positive** `c₁`. Its proof uses `c₁` as the discrepancy/error-budget constant; (5.8) selects `Kbold` sufficiently large relative to it, and later implicit-error absorptions increase fixed constants or thresholds. Equations (5.23)–(5.24) retain the explicit fractions `5c₁/12` and `c₁/4`. Nothing in that proof requires a lower bound on `c₁` independent of the fixed coefficient parameters. The compatibility enlargements (5.35) are then made for the regularity exponent `Adiv`.
4. The mass estimate (5.15) applies on the same resulting admissible range; its fixed lower constants and threshold can be packaged together with the truncated-mass estimate. Enlarging the common threshold is harmless.

**Logical boundary:** Step 3 is a rereading of the published proof with reselected constants, not a consequence by monotonicity of the already fixed statement of Proposition 5.2. Replacing `c₁` by a smaller constant weakens its discrepancy hypothesis as well as its conclusion. No Lean proof of this source-to-interface reparameterization, of the fixed-cutoff extension in Step 1, or of the resulting joint existence has been supplied. They are the bridge **KM-J**, included explicitly in any external joint input. The bridge does not assume a dense progression, sparse-prime discrepancy, recurrence iteration or any original conclusion of the supplied manuscript.

The actual implemented external predicate is `PSPrimes.KMTTCompatibleInput` in `PrimeMassInputs.lean`. Its type quantifies a fixed positive cutoff before selecting the compatible record:

```lean
∀ C : ℝ, 1 ≤ C → ∀ d ℓ : ℕ, 1 ≤ d → 1 ≤ ℓ → ∀ Adiv : ℕ,
  ∀ τmax : ℝ, 0 < τmax →
    ∃ p : KMTTComparisonParameters ℓ Adiv,
      KMTTUnweightedWitness C d ℓ Adiv p ∧
      Nonempty (PrimeProgressionMassWitness p d τmax)
```

This predicate has been compiled but is uninstantiated; compiling a proposition-valued definition does not prove it. Since τmax is quantified before the existential `p`, its fixed parameters may depend on τmax. In the actual application τmax is the displayed function of `C,d`, so the manuscript's fixed-parameter dependence is preserved. The recurrence theorem consumes this joint predicate together with SS, TV and weak regularity. The pointwise theorem does not consume it. The central assumption catalogue must record KM-J separately from the directly quoted statements KM-U, KM-R and KM-M. An independent second reading of raw source lines 2997–3907 confirmed the proof-level reparameterization; no formal proof of that bridge is claimed.
