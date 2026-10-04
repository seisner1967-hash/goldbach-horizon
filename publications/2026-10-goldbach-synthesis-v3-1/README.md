# Goldbach Synthesis V3.1

Durand Serge, 4 October 2026. Complete revised English V3 manuscript with
the completed native numerical addendum and a French, self-contained handoff.

- [Revised PDF](goldbach_synthesis_v3_1.pdf)
- [Standalone LaTeX](goldbach_synthesis_v3_1.tex) and [source ZIP](goldbach_arxiv_source_v3_1.zip)
- [Lightweight resumption package](goldbach_session_handoff_v3_1.zip)
- [Numerical addendum](numerical_addendum.txt) and [exact verdict](numerical_verdict.json)
- [French Fejer handoff](HANDOFF_FEJER_V3_1.txt)
- [Evidence registry](evidence_v3_1.json) and [document build receipt](build_receipt_v3_1.json)
- [Original V3, unchanged](goldbach_synthesis_v3.pdf) and [historical registry](evidence_v3.json)
- [Complete new numerical archive](../../research/goldbach-numerical-20261004/)
- [Historical V3 engineering corpus](../../research/goldbach-synthesis-v3-20261004/)

At N=100000000, K=2^27, the observed native CRT, direct canonical A32 sum and
auxiliary B40 reconstruction agree exactly. The normalized A32/B40 difference
is zero, with fixed joint quantization radius 4.4408921429095471e-8 < 1e-6.
The normalized integer is not an exact real-log coefficient or a Mellin
quadrature result. Native Lean refinement and the complete Mellin truncation
chain remain open, as do spectral H1, D_N and Goldbach.

This revision introduces no new theoretical research or Lean theorem.
The inventory remains 88 credited modules and 1488 auxiliary declarations,
including definitions. Historical STOP receipts are retained separately.

The PDF was exported with the existing cached Tectonic engine and rendered
for layout QA. The Codex built-in editor could not initialize platform
directories; its diagnostic is preserved separately. With a standard TeX
installation, compile the standalone source twice:

```console
pdflatex -interaction=nonstopmode -halt-on-error goldbach_synthesis_v3_1.tex
pdflatex -interaction=nonstopmode -halt-on-error goldbach_synthesis_v3_1.tex
```

See README_SOURCE_V3_1.txt for package requirements. The delivery ZIP is a
compact documentary entry point, not a replacement for the complete byte-exact
research archive. Its manifest and the repository restore helper recover
all large numerical payloads. Do not relaunch the full calculation merely
to recover the already documented verdict.
