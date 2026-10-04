# Goldbach Synthesis V3

Durand Serge, 4 October 2026. Engineering closure and theoretical research
handoff, continuing the [V2 synthesis](../2026-10-goldbach-framework/).

- [English PDF](goldbach_synthesis_v3.pdf)
- [Standalone LaTeX source](goldbach_synthesis_v3.tex)
- [Minimal arXiv source archive](goldbach_arxiv_source_v3.zip)
- [Evidence and status registry](evidence_v3.json)
- [Theory handoff](HANDOFF_THEORY_V3.txt)
- [Complete byte-exact engineering snapshot](../../research/goldbach-synthesis-v3-20261004/)

The paper separates independently compiled identities, exact rational arithmetic,
uncompiled analytic interfaces, and the unresolved signed margin for `D_N`.
It does not claim a proof of binary Goldbach or that the parity barrier has been
overcome. No new scientific execution was performed for this editorial closure.

The source is a standalone article with ordinary LaTeX packages and an inline
bibliography. No external figures, shell escape or private fonts are needed.
With a normal TeX installation, compile twice:

```console
pdflatex -interaction=nonstopmode -halt-on-error goldbach_synthesis_v3.tex
pdflatex -interaction=nonstopmode -halt-on-error goldbach_synthesis_v3.tex
```

The full snapshot retains failed attempts and historical wording as provenance.
The V3 manuscript and its explicit evidence classes govern the current claims.
The completed French edition is retained byte-exact in the snapshot's
`workspace/Goldbach_Parity_20261002/synthesis_v3/fr_archive/` directory.
