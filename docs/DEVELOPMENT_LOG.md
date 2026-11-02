# Development log

## 30 October 2026 — architecture and checked prerequisites

Read all 1,273 lines of the authoritative source before choosing modules.
Preserved its 45,569 bytes unchanged; SHA-256
`3876857aaa7855cc791df0be3b7b60bfbe0be249df013465dd50f72d1566a701`.
No PDF was supplied. Generated the original PDF and `.aux` numbering by
successful latexmk compilation: 14 pages, nine numbered statements and 39
numbered equations. No source/PDF disagreement was found.

Four substantial milestones: (1) definitions and algebra, (2) finite phase and
counting comparisons, (3) density increment and admissibility, (4) analytic
comparison and weight removal. These are mathematical dependency groups, not
claims that the corresponding manuscript sections are already formalized.

Installed official Lean 4.19.0 and exact Mathlib revision. The sandbox's numeric
proc executable path failed; an environment-only path-lookup shim fixed it.
No Lean kernel or binary was patched. Official dependency cache: 6,641 files.
An actual Mathlib import and small tactic proof passed. Logs retain initial
setup failures as well as successful commands.

Independent full-paper review found no demonstrated necessary mathematical
correction. Primary sources were checked for Shao–Sun, Teräväinen, the earlier
orbit estimate, KMTT, and MWW. KMTT's composite interface and MWW's finite-Lp
specialization remain explicit obligations. The optional no-Siegel footnote is
not used as an assumption.

Fresh project compilation checked definitions, polynomial rescaling (including
degrees and coefficient bounds), finite density estimates, exact counting
linearity, phase scaling, zero-phase mass, exponent arithmetic, Abel summation,
unweighting for selected-element enumeration, and Tonelli. No main-theorem
completion was inferred from these auxiliary proofs.

## Comparison and pointwise completion

The finite comparison was assembled using additive-character restriction to
progressions and an exact two-variable lift back to the fixed polynomial
family. The implementation proves its support bounds, floor-scale relations,
normalizations, the Q² loss and its absorption. The final c-range and power
saving are chosen with the required degree-only dependencies. Proposition 2.3
is derived from the named SS and VN inputs; it is not itself an assumption.

For Section 4, a discrete Abel transformation along the increasing enumeration
of selected primes replaces the manuscript's equivalent integral partial
summation calculation. Positive monotone weights and centered weighted sums
bounded by C+εW give an unweighted bound C/a₀+εn. Initial exceptional terms are
absorbed into C. Nat.nth constructs the enumeration; the exact reindexing,
cutoff cardinalities and infinitude from the mass asymptotic are proved.
Integer power cutoffs (j+1)^k suffice for the sparse-sequence argument. Their
strict increase, successive ratio, summable decay and the full-sequence
bracketing/interpolation are checked.

The actual orbit discrepancy L1 saving is derived from SS and the arbitrary
real-weight orbit estimate OR. Zero-phase SS and ordinary PNT give sparse
Mangoldt mass. The elementary higher-prime-power bound and exact prime/nonprime
decompositions then give the selected-prime weighted limits. Weight removal
and essential-L∞ normalization complete Theorem 1.2 with the same limit as the
ordinary-prime averages. Its external inputs remain SS, OR, PNT and MW, with
their unformalized source translations documented explicitly.

## Workspace reset and verified recovery

The transient workspace reset before a later archive had been saved. The first
saved project archive was restored. Missing source modules were reconstructed
from the original authored history, rather than replaced by mathematical
assumptions. The final `Pointwise.lean`, `OrbitComparison.lean` and
`MainPointwise.lean` matched their recorded pre-reset hashes byte for byte.
Other recovered modules with recorded hashes were likewise checked against
those records. The unchanged manuscript hash was preserved.

Recovered sources were rebuilt in the restored pinned runtime and central
theorems were audited again. These new runs are distinguished by the recovery
log filenames. Historical success logs were not presented as current builds;
failed setup attempts and interrupted runs were retained. Raw notes, including
the evolving partial-proof states, remain separately in `history/`.

## Quantitative recurrence completion

Primary-source KMTT inspection separated the two primitive inputs: ordinary
prime-to-unweighted discrepancy, and weak regularity with its small-scale
alternative, actual progression atoms and coordinate-dependent resolutions.
The original deduction of a denser atom is proved. Its length has an explicit
positive prefactor; the later normalization absorbs this prefactor through
permitted fixed parameter choices instead of setting it to one.

The comparison constant and prime-mass truncation must use compatible source
parameters. This led to the explicit KM-J joint-selection interface. Source
proof inspection supports rerunning the comparison proof after shrinking the
fixed discrepancy constant and enlarging permitted parameters. This is an
unformalized source-to-interface bridge, not a monotonicity deduction from an
arbitrary previous witness. The catalogue records it separately. No density
increment, PS-prime discrepancy or main conclusion is included in KM-J.

The actual Lemma 3.2 is obtained from the counting comparison, model interval
overlap, collision root counts, higher prime powers and uniform error
absorption. LogScales derives the logarithmic length recursion from the actual
finite progression-length inequality, retaining its positive prefactor and
separate modulus/density exponents. Its constant is chosen before all stage
variables; the initial density bounds every later density error.

RecurrenceConstruction stores genuine finite sets, positive integer sizes and
moduli, fixed smoothness/lcm data and the exact forbidden PS-prime pattern.
Each next set is the affine pullback onto the denser progression. The proof
constructs finite prefixes and derives the next stage's admissibility only
from the past prefix and its verified range. The initialization uses a full
residue-class intersection of at least the original density and the actual
floor length. The finite horizon and uniform logarithmic bookkeeping permit
enough multiplicative density gains to contradict density at most one.

The final `PSPrimes.quantitative_recurrence` theorem selects the actual largest
polynomial degree and a common coefficient bound, obtains compatible source
witnesses, and discharges the internal step provider. Its density exponent κ
is selected before c and the subsequent scale threshold. Thus Theorem 1.1 now
has a conditional proof with the manuscript's actual integer configuration,
PS-prime parameter and pairwise distinctness.

Exploratory whole-file checks were interrupted while many Lean compilations
ran concurrently. A trivial Mathlib probe showed the same delay; those runs
were not reported as successes. Serializing compilation resolved the delay
without a mathematical workaround. Targeted builds of RecurrenceConstruction
and MainRecurrence then passed, as did their five central theorem axiom audits,
with only propext, Classical.choice and Quot.sound. Separate source
correspondence reviews inspected the completed main statements and their
hypotheses. Raw implementation handoffs and reviewed-source hashes remain in
`history/`; this log summarizes the final verified state without replacing them.

## Final validation handoff

Both main theorems and all seven original numbered statements now have checked
conditional deductions; the two quoted analytic statements remain external.
No external input predicate has been instantiated. No new mathematical axiom
or proof placeholder was introduced. The final project-wide serial clean
build and comprehensive audit are a separate last verification step; their
outcome must be recorded only after the actual commands finish. At this
handoff, the successful results are the targeted builds and audits listed in
`docs/RESTART.md`, not an unrun final clean check.

## Final clean validation and delivery

After freezing all production proof sources, the actual command
`source ../tooling/env.sh && bash scripts/check.sh` completed with exit 0 on
30 October 2026. The script removed only the project build directory, then
compiled all 45 modules and the entry point serially. Every one of the 46
recorded target commands succeeded; the target invocations took 324.137
seconds in total. Dependency artifacts came from the pinned official Mathlib
cache, not a fresh dependency rebuild.

The comprehensive generated audit checked 455 named declarations and exited
0, with only Classical.choice, Quot.sound and propext observed. The production
source scan and original manuscript SHA check passed. Final production source
hashes and the final correspondence review hashes were separately checked.
An older recurrence-review hash for Definitions differs solely because its
status comments were updated; the final review records the current source
hash. Earlier review records and unsuccessful/interrupted commands remain
historical, not final verification evidence.

Both blueprints and the complete 48-label statement map now agree with the
seven checked conditional deductions and two quoted external inputs. The
project is delivered with no open original numbered proof under those explicit
premises; external theorems and the named source-formulation bridges remain
unformalized. See evidence/VERIFICATION.md for the final proof and document
checks. Historical drafts and raw notes are preserved separately.

Final document checks also passed: all 35 blueprint-exported Lean names checked
against the compiled project, all eight external interfaces and seven theorem
signatures printed/checked, and every one of the manuscript's 48 active labels
appeared exactly once in the statement map. Both PDFs compiled, native
leanblueprint generated its dependency metadata, and all pages were visually
checked: compact 8 pages, full exposition 17 pages. The final archive includes
their LaTeX sources, PDFs and actual verification logs.

## Removing the independent own-paper orbit assumption

The author supplied the complete source of *Polynomial configurations and
pointwise averages along Piatetski–Shapiro sequences* and requested that the
prime project no longer depend on an unformalized result from that paper.
The source was read in full and preserved unchanged under
`manuscript/related-original/PSSequences.tex`. The exact needed part is
Proposition 1.4 (`p:orbit`), not the second paper's main theorems.

The proof derives its orbit bound directly from the finite Teräväinen input
already used by the prime project's counting argument: choose bounded
representatives and the explicit L1 dual multiplier, average over an integer
spatial interval of length N^d, apply finite VN to exactly supported orbit
samples, and integrate. The same degree-only K is retained. Polynomial
translation by −1 preserves degrees; support constants must precede N and
the system. Integrability and essential bounds are proved rather than
included in a new external assumption. The target is a proved implication
`FiniteVNInput → OrbitVNInput` and a revised public main theorem with no
independent OR premise. This entry records the plan, not a proof completion.

The new `orbitVNInput_of_finiteVNInput` theorem has now compiled successfully.
Its supporting polynomial and measure modules also compiled. A dedicated
eight-declaration dependency audit passed with only the standard logical
axioms. The implementation applies the finite estimate on one almost-everywhere
set where every integer iterate of every input is 1-bounded; it therefore
retains the original essential representatives directly, without requiring
new pointwise-bounded hypotheses.

The public `ps_orbit_discrepancy_L1_gamma`, `ps_orbit_comparison_gamma`,
`ps_orbit_comparison` and `pointwiseErgodicTheorem_of_external_inputs`
declarations have been revised to take `FiniteVNInput` instead of an
independent `OrbitVNInput`. `lake build PSPrimes.MainPointwise` passed for
the revised dependency chain. The central orbit transfer is a proved lemma,
not a new external bridge. The latest complete clean check is being rerun;
the earlier 45-module/455-declaration results are retained under
`history/before-orbit-verification/` as baseline evidence.

### Orbit-extension final verification

After proof-source freeze, the actual command
`source ../tooling/env.sh && flock /tmp/psprimes-orbit-lean.lock bash scripts/check.sh`
completed with exit 0. The clean build freshly compiled all 48 project modules
and the entry point; all 49 recorded target commands exited 0, taking 391.937
seconds in total. Dependency artifacts were reused from the same pinned
Mathlib cache. The generated audit checked all 481 named declarations and
exited 0 with only Classical.choice, Quot.sound and propext. The production
forbidden-token scan, both preserved manuscript hashes, final production
source hashes and six independently reviewed extension-source hashes passed.

The actual public-interface check and all 36 blueprint declaration checks
also exited 0. Updated compact/full PDFs compiled to 9/18 pages; native
leanblueprint metadata resolved all dependencies, and all 27 pages were
rendered and visually checked. The precise new scope is the required
real-weight, essentially 1-bounded specialization of the related manuscript's
Proposition 1.4, including its application translations. Its unrelated main
results are not claimed formalized. The prime pointwise theorem now has no
independent result from the author's other paper as a premise. Seven
independent deep external interfaces and the remaining named source bridges
are retained in the catalogue. The final downloadable archive and both PDFs
are updated versions of the existing deliverables.


## 2 November 2026 — revised manuscript and lacunary variation

Read the complete revised source and compared it with repository commit
d523ab6. Main theorems are unchanged; Corollary 4.2 is the new mathematical
conclusion. The endpoint remark remains conjectural. Restored the same pinned
Lean/Mathlib environment and freshly built the original library before adding
four modules. Proved the exact infinite variation seminorm and real finite-chain
correspondence, measurability, Minkowski/perturbation bounds, arbitrary lacunary
geometric summation, and exact essential-norm homogeneity including zero factors.
Transferred the existing all-N discrepancy rate using separately documented
MWW variational input MW-V. No own-paper assumption was added. An intermediate
concurrent build failed during development; its unedited output is historical.

Final clean check passed: 53 target commands, 340.932 seconds, 508 declarations
in the axiom audit, only the three standard axioms. All three manuscript hashes
passed, and 46 blueprint names checked. Both updated blueprints compile (10/20
pages), with native dependency metadata and rendered visual QA. AI mathematical
review found no serious correspondence issue; independent human review remains
outstanding. Preserved original and revised manuscripts and earlier documentation.
The η sentence and eight-interface acknowledgement replacements are documented.
Prepared an additive ZIP overlay and the updated complete project for download;
the author will upload to GitHub. No remote push was performed.
