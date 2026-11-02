# The two blueprints

- `src/compact.tex` / `src/compact.pdf`: primary reading guide.
- `src/full.tex` / `src/full.pdf`: detailed exposition of the same argument.
- `src/orbit-transference.tex`: the checked finite-to-orbit deduction needed from the related paper.
- `src/content.tex`: shared mathematical statements and proof architecture; the `Detailed` flag adds the longer derivations.
- `src/correspondence.tex` and `src/catalogue.tex`: common manuscript map and external-input catalogue.
- `src/web.tex`: native leanblueprint web entry point, with a dependency graph generated from the metadata.

The current manuscript is the unedited revision supplied on 2 November 2026,
preserved in `manuscript/revised-2026-11-02/Draft.tex`. Its generated PDF has
15 pages. It retains the 48 earlier labels and adds `c:long-variation`;
there are ten labelled theorem-like statements, 39 labelled equations and
one unlabelled numbered endpoint Remark 1.3. That remark shifts the quoted
Teräväinen theorem from 1.3 to 1.4.

All seven earlier deductions and new Corollary 4.2 have checked conditional
proofs. Theorems 1.4 and 2.1 are quoted externally. Eight explicit external
input interfaces remain uninstantiated, including the new MW-V variation
specialization of MWW Theorem 1.1(iv). The original two main theorems still
jointly use six interfaces. The required orbit transference from the
author's related sequences paper remains proved from finite VN. The new
variation proof uses SS, TV and MW-V; its geometric summation, infinite
supremum, measurability and exact essential-norm product are proved
internally. See `src/revision-variation.tex` for the extension and
`docs/ASSUMPTIONS.md` for the precise external bridges.

Both versions share the statement map, catalogue and revision section.
Earlier source/PDF/document checkpoints are preserved under `history/`,
including `pre-revision-2026-11-02/`. Neither supplied manuscript is edited
by the blueprint. Two small expository manuscript replacements (the missing
η introduction and the updated acknowledgement count) are in
`docs/REVISION_2026_11_02.md`. No theorem correction has been identified.

## Build

From `blueprint/src`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error compact.tex full.tex
python -m pip install leanblueprint==0.0.20
plastex --config=plastex.cfg web.tex
```

The checked environment used leanblueprint 0.0.20, plasTeX 3.1 and plastexdepgraph 0.0.5. PDF compilation used the installed pdfTeX/LaTeX distribution. The upstream `blueprint.sty` and the upstream print-metadata implementation are included; `uses` and `proves` therefore use genuine supported leanblueprint/depgraph metadata rather than invented tags. Printable metadata checks label references. Native plasTeX successfully generated `blueprint/web/dep_graph_document.html` and `blueprint/lean_decls`.

The PDFs build without overfull boxes or undefined references. Native web generation succeeds. Its optional vector-imager discovery reports missing `dvisvgm`; the declaration graph and MathJax output are still generated. Native HTML is supplementary to the requested PDFs. Declaration names are exported in `blueprint/lean_decls`; this repository has no published declaration-documentation site, so do not treat automatically generated documentation URLs as evidence that a declaration is in Mathlib. Configure `dochome` after generating and hosting actual declaration documentation.

Build logs and representative rendered pages are in `evidence/blueprint/`. The final status is reconciled with the checked theorem names and project map. The blueprint marks no external analytic assertion as a kernel theorem.
