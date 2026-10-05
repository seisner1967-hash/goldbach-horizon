# Document build

Author: Durand Serge.

The portable source bundle includes main.bbl, references.bib, report.bst and
the figure. Extract it into a new directory and compile main.tex there.
The article uses only amsmath, amssymb, amsthm, booktabs, hyperref and graphicx.
Its font declarations use standard Type1 Latin Modern metrics.

For an existing PDFLaTeX installation:

```text
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

PDFLaTeX was unavailable during this preparation. The actual PDF and bibliography
were generated with cached Tectonic 0.17.0 and BibTeX 0.99d; the document review
records the exact engine and source/output hashes. No installation was performed.
The included main.bbl is actual compiler output, not a manually fabricated file.

The saved compile_paper.py accepts --engine and --cache-source for an existing
Tectonic executable and cache. It copies a fresh document snapshot and writes
temporary files only under paper/_compile/. Temporary files are excluded from
the publication commit. The table and evidence-map scripts consume existing
artifacts only; their use does not confer new mathematical credit.

See A6_COMPILE_CLAIM_REVIEW.json, A5_REVIEW.json, PDF_VISUAL_REVIEW.json and
REVIEW_CHECKLIST.md for document checks and their limits.
