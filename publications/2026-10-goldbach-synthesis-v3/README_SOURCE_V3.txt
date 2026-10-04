Goldbach Synthesis V3 - standalone article
Durand Serge, 4 October 2026.
English edition; the completed French snapshot is retained in fr_archive/.

This manuscript closes an engineering step and records its proof boundary.
It is not a proof of binary Goldbach and does not claim to overcome parity.

The source is one UTF-8 .tex file. Its bibliography is inline; no external
figures, private fonts, shell escape, Lean execution, or BibTeX is required.

Normal TeX Live or MiKTeX build, run twice:
  pdflatex -interaction=nonstopmode -halt-on-error goldbach_synthesis_v3.tex
  pdflatex -interaction=nonstopmode -halt-on-error goldbach_synthesis_v3.tex

The exported PDF uses the existing local Tectonic engine and cached resources.
The built-in source editor was retained. Its compiler returned a platform
directory configuration error, recorded in builtin_latex_diagnostics.json;
the failure did not identify a manuscript source error.

Evidence boundaries:
  88 modules / 1488 auxiliary declarations, including definitions;
  exact main Mellin module PASS: 24 theorems + 6 definitions;
  exact rational scalar upper bound PASS at N=10^8;
  complete Mellin coefficient error interface remains uncompiled;
  last native coefficient check stopped without a verdict;
  D_N signed bound and the research win condition remain open.

The arXiv source archive supplies the .tex and this file. It is source-ready;
no arXiv submission, moderation decision or external peer review is claimed.

For a fresh theory conversation, read HANDOFF_THEORY_V3.txt and the V3 PDF.
Historic sources, receipts, logs and unsuccessful attempts are preserved in
the accompanying full byte-exact research snapshot.
