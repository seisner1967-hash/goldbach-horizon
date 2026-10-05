"""Add publication pointers without altering the previous README bytes.

Run from the repository root. Only README.md and CITATION.cff are written.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HEADER = """## Negative-results and formalization report, 5 October 2026

Author: **Durand Serge**, Independent researcher.

- **Proved in Lean:** the generated inventory records established auxiliary
  declarations with their hypotheses and existing credit; no Goldbach proof is claimed.
- **Conditional:** retained external hypotheses and excluded material are identified
  in Appendix B.
- **Open:** the signed analytic estimate, the uncovered range and the uniform
  certificate construction remain obligations within their respective frameworks.
- **Negative results:** the report records obstructions to specified arguments and
  constraint families; it does not exclude either whole route.

[Report (PDF)](paper/main.pdf) · [Portable source](paper/main.tex) ·
[arXiv bundle](paper/arxiv_submission.tar.gz) ·
[Evidence map](paper/evidence_map.json) · [Human review checklist](paper/REVIEW_CHECKLIST.md)

Complete declaration tables: [analytic inventory](paper/analytic_lean_inventory.csv)
and [algebraic inventory](paper/algebraic_lean_inventory.csv).
The paper derives these tables from existing records without new mathematical runs.
Large binary evidence is excluded from this publication commit; its recorded hashes
are retained for a separate author-managed GitHub Release or Zenodo deposit.

---

"""
assert len(HEADER.splitlines()) <= 50
path = ROOT / "README.md"
original = path.read_bytes()
header = HEADER.encode("utf8")
assert not original.startswith(header), "Publication header already present"
path.write_bytes(header + original)
assert path.read_bytes()[len(header):] == original
(ROOT / "CITATION.cff").write_text('''cff-version: 1.2.0
message: "Please cite the negative-results and formalization report."
type: article
title: "Obstructions and Formalized Identities in Two Binary Goldbach Research Programmes: A Negative-Results and Formalization Report"
authors:
  - family-names: Durand
    given-names: Serge
    affiliation: Independent researcher
    email: seisner1967@gmail.com
date-released: 2026-10-05
url: "https://github.com/seisner1967-hash/goldbach-horizon"
repository-code: "https://github.com/seisner1967-hash/goldbach-horizon"
keywords:
  - binary Goldbach
  - formalization
  - negative results
  - Lean
  - Nullstellensatz
''', encoding="utf8", newline="\n")
print("README publication header:", len(HEADER.splitlines()), "lines; previous bytes preserved")
