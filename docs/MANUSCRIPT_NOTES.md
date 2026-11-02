# Manuscript review and corrections

## Current revision supplied 2 November 2026

The author's revised source is preserved unchanged in
`manuscript/revised-2026-11-02/Draft.tex`, SHA256
`1b471706e66ddad262f9e7b3d3954336710112b9f962a07831b7b681df1c9fdd`.
Its locally compiled PDF has 15 pages. Corollary 4.2 adds the weighted
lacunary r-variation estimate; Remark 1.3 records a conjectural finite-Lp
extension and endpoint background. The two main theorems retain their
hypotheses and conclusions. No mathematical counterexample or necessary
change to the new corollary has been identified.

Two short expository updates are needed in the revised manuscript: restore
the sentence introducing η after the shortened prime-power bound, and
change the acknowledgement count from seven to eight for this extended
Lean development. The exact replacements, their rationale and the new
formalization boundary are in [REVISION_2026_11_02.md](REVISION_2026_11_02.md).
The supplied source is not edited in place.

## Historical review of the original 30 October source

No necessary mathematical replacement has been demonstrated. The preserved
`manuscript/original/Draft1.tex` is unchanged. No separate author-supplied PDF
was attached; the generated 14-page PDF agrees with the source numbering.
The project therefore supplies no “replace this with this” mathematical
correction. Unformalized deep external inputs are limitations of the project,
not demonstrated errors in the manuscript.

All nine numbered statements are accounted for: seven have checked
conditional deductions, and Theorems 1.3 and 2.1 are explicitly quoted
external interfaces. [PAPER_MAP.md](PAPER_MAP.md) covers every numbered
statement, all 39 numbered equations, and substantial unnumbered steps.
External theorems and source-to-interface bridges remain identified in
[ASSUMPTIONS.md](ASSUMPTIONS.md). Final clean-build and audit claims must
be read from actual command evidence, separately from this review.

The complete-paper review paid particular attention to these points:

- The progression sum has endpoint QM+1, and the included n=1 term vanishes.
  The checked proof shrinks the saving before γ and proves endpoint absorption.
- The changing family is lifted to the fixed original polynomials. Both
  variable reindexings, support changes, and the Q² cost are exact.
- The coefficient condition holds for all positive moduli. Collision roots
  and actual higher prime powers are separated and bounded elementarily.
- The KMTT discrepancy constant and classical mass cutoff are selected
  jointly. This compatibility remains external KM-J; it is not inferred
  from unrelated existentials or a stronger unverified no-Siegel estimate.
- The original local density-increment argument is proved from separate
  comparison and weak-regularity witnesses. A checked enlargement of K₁
  and one extra inverse modulus power remove the positive length prefactor,
  preserving literal Proposition 3.1.
- Initialization uses a full residue-class intersection with its actual
  floor length. Each subsequent set is an actual affine pullback, with
  Q_{j+1}=Q_j^(b_j+1), and exact forbidden-configuration transport. Current
  admissibility is derived from already built prefixes before invoking the
  next increment. κ is chosen before c.
- The orbit proof derives its L1 saving, summable-subsequence convergence,
  and full-sequence interpolation. Actual mass limits justify gap bounds.
- Higher prime powers are removed before discrete Abel unweighting. Count
  divergence and finite zero denominators are handled. Bounded representatives
  and all integer iterates recover essential L∞ hypotheses, with one common
  a.e. limit for both actual averages.

These checks found no necessary change to the author's hypotheses,
normalizations, parameter order, or conclusions. The optional recent
no-Siegel footnote is unused. No numerical experiment was needed to settle
a demonstrated uncertainty, and no finite computation is offered as proof
of a general analytic estimate.

Optional editorial observation only: the final paragraph of Section 1 says
“the subsequent version of the ergodic theorem”; “the unweighted version”
would identify the intended step more directly. The original is unchanged.

The subsequent supplied sequences manuscript is preserved separately under
`manuscript/related-original/`. Its Proposition 1.4, equation (10), supplies
the argument for the orbit estimate used here. That needed real-weight,
essentially 1-bounded specialization is now proved from finite Teräväinen VN
in `OrbitTransference.lean`, including its shift/support and measure-theoretic
application steps. Theorem 1.2 now uses finite VN directly and has no
independent premise from that other paper. This removes the earlier external
OR and OR-B entries without changing either prime-paper main specification.
The unrelated arguments and main results of the sequences paper are outside
this extension.
