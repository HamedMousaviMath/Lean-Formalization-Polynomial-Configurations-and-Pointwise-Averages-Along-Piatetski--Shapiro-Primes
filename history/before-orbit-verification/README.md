# Polynomial configurations and pointwise averages along Piatetski–Shapiro primes

Lean 4 formalization of the supplied 14-page paper by Hamed Mousavi.
**All seven original numbered deductions, including both main theorems, have
checked conditional proofs.** The two quoted analytic statements remain external
inputs. This is a conditional formalization of the paper's deductions;
the external inputs and their documented source-to-interface translations
have not themselves been formalized or instantiated.

| Manuscript conclusion | Checked Lean declaration | External input families |
| --- | --- | --- |
| Theorem 1.1: configurations with pairwise distinct terms and a PS-prime parameter | `PSPrimes.quantitative_recurrence` | SS, VN, KM-R, KM-J |
| Theorem 1.2: almost-everywhere convergence of the actual PS-prime averages, with the ordinary-prime limit | `PSPrimes.pointwiseErgodicTheorem_of_external_inputs` | SS, OR, PNT, MW |

The declarations retain the manuscript's quantifier order, integer intervals,
polynomial families, parameter ranges, cardinality denominators and essential
boundedness hypotheses. [The statement map](docs/PAPER_MAP.md) records each
numbered statement and the substantial intermediate claims.
[The assumption catalogue](docs/ASSUMPTIONS.md) gives the precise Lean
interfaces, references, dependencies and unproved translations. In particular,
KM-J explicitly records the compatible selection of KMTT comparison and
classical prime-mass constants; no arbitrary parameter record is assumed to
have those properties.

## Build and audit

Install elan and run from the project root:

```sh
lake exe cache get
bash scripts/check.sh
```

The project pins Lean **4.19.0** and Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; `lake-manifest.json` pins the
transitive dependencies. The check script removes only this project's compiled
artifacts, compiles all project sources, scans production sources for forbidden
proof placeholders and shortcuts, and runs `#print axioms` on the named project
declarations. Mathlib dependency artifacts are reused from its official cache;
they are not claimed to have been freshly rebuilt.

The final clean build passed for all 45 project modules and the entry point.
All 455 named project declarations passed the axiom audit, which reported only
`propext`, `Classical.choice` and `Quot.sound`; the production placeholder scan
and manuscript integrity check also passed. See
[the verification evidence](evidence/VERIFICATION.md) for actual commands,
source hashes and outcomes. A dependency audit checks logical dependencies; it does
not establish the truth of explicit theorem parameters or faithful manuscript
correspondence. Those are documented and reviewed separately.

The sandbox used an environment-only executable-path compatibility shim;
ordinary installations do not need it. Its source and explanation are in
`scripts/environment/`, with the actual environment record in
`evidence/ENVIRONMENT.txt`. The Lean binary and kernel were not modified.

## Read the project

- [Statement map](docs/PAPER_MAP.md): manuscript numbering, declarations and scope.
- [Assumption catalogue](docs/ASSUMPTIONS.md): exact external inputs and references.
- `blueprint/`: compact and detailed expository blueprints, LaTeX sources and PDFs.
- [Restart record](docs/RESTART.md): authoritative source, verification and next task.
- [Development log](docs/DEVELOPMENT_LOG.md): one chronological account of the work.
- `history/`: retained raw development notes, earlier blueprint state and reviews.
- `evidence/`: build logs, generated audit source and dependency-audit output.

`manuscript/original/Draft1.tex` is the unchanged authoritative source. No
version, date or PDF was supplied; its generated PDF has 14 pages. No necessary
manuscript correction has been demonstrated; review notes are in
[MANUSCRIPT_NOTES.md](docs/MANUSCRIPT_NOTES.md).

No original conclusion is assumed to complete its proof. External results are
explicit predicates and theorem parameters, not added mathematical axioms.
Production proofs contain no `sorry`, `admit`, `unsafe` or `native_decide`.
