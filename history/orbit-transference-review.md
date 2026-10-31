# Independent review: removing the earlier-paper orbit assumption

Reviewer: `/root/orbit_review`, 30 October 2026.

This review concerns the newly supplied manuscript *Polynomial configurations
and pointwise averages along Piatetski–Shapiro sequences*, specifically the
proposition with label `p:orbit` and display `e:orbit-transfer`. It is distinct
from the authoritative primes manuscript preserved in `manuscript/original/`.
The user requests at least the part needed for the primes paper, retaining
the previously permitted deep external inputs.

## Required scope

The exact target is to derive the existing `OrbitVNInput` specification from
`FiniteVNInput`, and hence remove an independent premise asserting an estimate
from the author's earlier paper. This target is an arbitrary-real-weight,
essentially 1-bounded, probability-space specialization. It includes genuine
integrability, the shifted evaluation `P_i(n−1)`, a degree-only exponent chosen
before the polynomial family, and a fixed-family constant chosen before the
system, cutoff, weight, magnitude and phase bounds.

No fractional-power estimate, Vaaler approximation, Shao–Wang counting theorem,
KMPWW theorem, recurrence theorem, or other main conclusion of the supplied
earlier manuscript is needed for this deduction. Those are outside the present
extension. A project-wide search identified no other independent assumption
from this earlier paper. KMTT is a separate, explicitly permitted external
input, even though it is coauthored by the same author.

## Mathematical proof reviewed before implementation

Fix a maximum degree `d≥1`, and take the exponent `K` supplied by finite VN.
For the fixed family put `R_i(y)=P_i(y−1)`. Composition by `y−1` preserves
each degree, its positivity, strict ordering and the maximum degree. A sum of
absolute values of coefficients gives a constant `C₀≥1`, depending only on
this fixed family, with

```
|a + R_i(n)| ≤ C₀ N^d
```

whenever `N≥1`, `1≤n≤N`, and `1≤a≤N^d`. This bound includes `n=1`, the
polynomials' possibly nonzero constant terms, negative evaluations and both
endpoints of the spatial interval.

First use everywhere 1-bounded representatives. For the finite weighted orbit
average `A(x)`, set `h(x)=conj(A(x))/‖A(x)‖`, with value zero at a zero of
`A`. Then `|h|≤1` and `h(x)A(x)=‖A(x)‖`, regarded as a real complex number.
All these functions are measurable up to null sets and integrable: `A` is a
finite sum of bounded measurable orbit products and the measure is finite.

Measure preservation gives

```
∫ h A = ∫ (1/N^d) Σ_{1≤a≤N^d} h(T^a x) A(T^a x).
```

For each fixed `x`, define `F₀(a)=h(T^a x)` on the integer interval
`[1,N^d]` and zero elsewhere. Define each `F_i(b)=f_i(T^b x)` on the
common spatial interval of radius `C₀N^d`, zero elsewhere. These functions
are genuinely 1-bounded and finitely supported where required. The preceding
support estimate shows their finite polynomial form equals the integrand's
spatial average exactly. The normalization is
`N^(−d−1) = (N^d N)⁻¹`; no boundary term or limiting transfer is present.

Apply the proved homogeneous finite VN bound to `g/B`. Its every-phase bound
is exactly the existing `PhaseBound d N g (N*E)`, so no additional supremum
or nilsequence bridge is needed here. The resulting pointwise bound is

```
C B (N⁻¹ + E/B)^(1/K).
```

Integrating and using total mass one proves the desired L1 bound with the
same `K` and constant independent of the system and cutoff. Finally restore
the original essentially bounded representatives using almost-everywhere
agreement simultaneously along all countably many integer iterates. Finite
averages agree almost everywhere, their integrability transfers and their
integrals of norms agree.

## Implementation review status

The mathematical deduction above passes the initial review. Implementation
and compilation are in progress; this file does not yet assert a checked Lean
proof or a successful final build. A final source review will be appended once
the implementation is available. No external premise equivalent to the orbit
bound is justified or introduced by this review. The finite VN source theorem
and its already catalogued formulation bridge remain external.

## Final signed source review

Reviewer: `/root/orbit_review`, 30 October 2026. The preceding initial status
is retained as history and is superseded by this final source review. I read
the complete frozen implementations in `OrbitPolynomials.lean`,
`OrbitMeasureHelpers.lean` and `OrbitTransference.lean`, including the proof
of `orbitVNInput_of_finiteVNInput`. **Mathematical correspondence passes.**

The implementation proves the exact existing `OrbitVNInput` specification
from `FiniteVNInput`; it does not assume that orbit estimate. Its finite
spatial restriction is an actual `Finsupp` on the integer interval `[1,N^d]`.
The support-sum extension is exact even when some values of the dual
multiplier vanish. The other functions are cut off at the fixed coefficient
sum radius, and both the unshifted spatial support and all shifted samples
are bounded by that radius. The shifted polynomial retains the entire
constant coefficient at the endpoint `n=1`, and its degree is unchanged.
The exact normalizing factors are checked algebraically with no limiting
argument or omitted endpoint term.

The chosen `K` is precisely the witness supplied by finite VN for the maximum
degree. The fixed-family support radius and finite-VN constant are chosen
before the probability space, integer action, functions, cutoff, weight, and
the bounds `B,E`. Thus this proof has the uniformity required by the subsequent
Shao–Sun application. It adds no hidden family- or system-dependent loss in
the saving exponent.

Instead of replacing representatives, the completed implementation uses the
already proved countable intersection over every integer iterate. On this
single full-measure set, all spatial functions are everywhere 1-bounded as
functions of the integer spatial variable. This directly retains the given
essentially bounded representatives. Integrability of the actual finite
average is proved separately from AEStrong measurability, preservation of
null sets, the essential bound, finite sums and the finiteness of the measure.
The explicit complex multiplier satisfies `h*A=‖A‖`, including at zero.
Translated dual pairs are integrable, so the finite-sum interchange and
measure-preserving change of variables used to compute the integral do not
rely on the undefined-integral convention. The last integral estimate uses
the actual probability mass one.

The implementation owner confirmed a successful actual command
`lake build PSPrimes.OrbitTransference`, and its saved build log was read.
The separate helper audit log was also read and has only `propext`,
`Classical.choice` and `Quot.sound`. This reviewer did not run a compiler;
the complete final project clean build and comprehensive audit are separate
checks to be reported by the integration owner.

Reviewed frozen source hashes are saved in
`history/orbit-transference-reviewed-sources.sha256`. This review discharges
the earlier-paper dependency OR and its former translation bridge OR-B at the
level of the required derived specification. Final public main theorems and
documents must use that derivation internally rather than retaining OR as an
independent external premise. The deep finite VN theorem and its TV-B source
formulation remain external. This extension formalizes precisely the part of
the supplied earlier manuscript needed here; it is not a formalization of
that manuscript's unrelated recurrence and fractional-power arguments.

## Public theorem integration review

I also reviewed the changed public statements and proof calls in
`OrbitComparison.lean` and `MainPointwise.lean`, together with the revised
comments in `OrbitInputs.lean`. All three `ps_orbit_*` public declarations now
take `FiniteVNInput`; the first L1 stage obtains its entire orbit specification
by `orbitVNInput_of_finiteVNInput hVN`. Subsequent stages pass the same finite
VN premise through that checked chain. The mapped Theorem 1.2 declaration
`pointwiseErgodicTheorem_of_external_inputs` now has exactly the substantive
premises Shao–Sun, finite Teräväinen VN, ordinary PNT and MWW ordinary-prime
pointwise convergence. Its target specification is unchanged.

The remaining local argument named `hOR` in the elementary arithmetic
absorption lemma is a fixed-system inequality supplied by the proved
transference; it is not an independent external premise of any public
`ps_orbit_*` or main theorem. Retaining the definition `OrbitVNInput` therefore
retains a convenient derived specification, not an assumed assertion from the
other paper. The source-to-interface bridge OR-B is fully replaced by the
new internal argument. The integration review passes; its six current source
hashes are included below. Compilation of the changed public modules and the
final clean build remain separately recorded by the integration owner.
