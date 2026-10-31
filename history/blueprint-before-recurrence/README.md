# The two blueprints

- `src/compact.tex` / `src/compact.pdf`: primary reading guide.
- `src/full.tex` / `src/full.pdf`: detailed exposition of the same argument.
- `src/content.tex`: shared mathematical statements and proof architecture; the `Detailed` flag adds the longer derivations.
- `src/correspondence.tex` and `src/catalogue.tex`: common manuscript map and external-input catalogue.
- `src/web.tex`: native leanblueprint web entry point, with a dependency graph generated from the metadata.

The manuscript's nine statement numbers and source labels are retained. Theorem 1.2, Lemma 2.2 and Propositions 2.3 and 4.1 have checked conditional proofs. Only Theorem 1.1, Proposition 3.1 and Lemma 3.2 remain open among original arguments; Theorems 1.3 and 2.1 are external. The five central input predicates are uninstantiated, with TV-B, OR-B and MW-B formulation bridges separately external. Main-conclusion definitions are specifications, not proof substitutes. Four milestones match the project map: objects/algebra, finite comparison, recurrence, pointwise convergence.

The original manuscript was compiled to 14 pages. No separately supplied PDF was available. The blueprint sources never modify the preserved manuscript. No demonstrated mathematical error requiring a replacement was found at this checkpoint.

## Build

From `blueprint/src`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error compact.tex full.tex
python -m pip install leanblueprint==0.0.20
plastex --config=plastex.cfg web.tex
```

The checked environment used leanblueprint 0.0.20, plasTeX 3.1 and plastexdepgraph 0.0.5. PDF compilation used the installed pdfTeX/LaTeX distribution. The upstream `blueprint.sty` and the upstream print-metadata implementation are included; `uses` and `proves` therefore use genuine supported leanblueprint/depgraph metadata rather than invented tags. Printable metadata checks label references. Native plasTeX successfully generated `blueprint/web/dep_graph_document.html` and `blueprint/lean_decls`.

The PDFs build without overfull boxes or undefined references. Native web generation succeeds. Its optional vector-imager discovery reports missing `dvisvgm`; the declaration graph and MathJax output are still generated. Native HTML is supplementary to the requested PDFs. Declaration names are exported in `blueprint/lean_decls`; this repository has no published declaration-documentation site, so do not treat automatically generated documentation URLs as evidence that a declaration is in Mathlib. Configure `dochome` after generating and hosting actual declaration documentation.

Build logs and representative rendered pages are in `evidence/blueprint/`. Mathematical status must be reconciled with the final project build and theorem map before marking more nodes checked. The blueprint marks no external analytic assertion as a kernel theorem.
