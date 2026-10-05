"""Review the compiled document and its links to existing recorded evidence.

Run after compile_paper.py. This is a document/claim review, not a new Lean
build, solver run, mathematical audit or grant of research credit.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re
from pypdf import PdfReader

PAPER = Path(__file__).resolve().parent
ROOT = PAPER.parent


def strict(path):
    def unique(pairs):
        data = {}
        for key, value in pairs:
            if key in data:
                raise ValueError("Duplicate JSON key " + key)
            data[key] = value
        return data
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def digest(path):
    raw = path.read_bytes()
    return {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}


def main():
    compilation = strict(PAPER / "_compile" / "latest_compile.json")
    assert compilation["exit_code"] == 0
    for name, expected in compilation["source_files"].items():
        assert digest(PAPER / name) == expected, "Source changed after compile: " + name
        assert b"\r" not in (PAPER / name).read_bytes(), "New source is not LF: " + name
    for name, expected in compilation["figure_files"].items():
        assert digest(PAPER / name) == expected
    for name, expected in compilation["outputs"].items():
        assert digest(PAPER / name) == expected
    run = PAPER / compilation["run_directory"]
    log = (run / "main.log").read_text(encoding="utf8", errors="replace")
    blg = (run / "main.blg").read_text(encoding="utf8", errors="replace")
    assert "error message" not in blg.lower() and "couldn't" not in blg.lower()
    assert not re.search(r"(?:Citation|Reference).*undefined", log)
    assert "There were undefined references" not in log
    assert "multiply defined" not in log
    assert "Rerun to get cross-references right" not in log
    assert "LaTeX Font Warning" not in log and "Missing character" not in log
    overfull = re.findall(r"Overfull[^\n]+", log)
    assert not overfull, "Repair layout warnings before final review: " + repr(overfull)

    evidence = strict(PAPER / "evidence_map.json")
    claims = evidence["claims"]
    ids = [claim["id"] for claim in claims]
    assert len(ids) == len(set(ids))
    sources = {}
    for claim in claims:
        assert claim["evidence"], claim["id"]
        for item in claim["evidence"]:
            path = Path(item["path"])
            assert not path.is_absolute() and ".." not in path.parts
            assert re.fullmatch(r"[0-9a-f]{64}", item["sha256"])
            binding = digest(ROOT / path)
            assert binding["sha256"] == item["sha256"], item["path"]
            if "bytes" in item:
                assert binding["bytes"] == item["bytes"], item["path"]
            sources[(item["path"], item["sha256"])] = item
    tex = "\n".join((PAPER / name).read_text(encoding="utf8")
                    for name in compilation["source_files"] if name.endswith(".tex"))
    used = {key for key in re.findall(r"\\(?:ev|evidence)\{([^{}]+)\}", tex)
            if not key.startswith("#")}
    assert used <= set(ids)
    cited = {key.strip() for group in re.findall(r"\\cite\{([^{}]+)\}", tex)
             for key in group.split(",")}
    bbl = (PAPER / "main.bbl").read_text(encoding="utf8")
    bibliography_keys = set(re.findall(r"\\bibitem\{([^{}]+)\}", bbl))
    verified = strict(PAPER / "bibliography_verification.json")
    assert cited == bibliography_keys
    assert cited <= {item["citekey"] for item in verified["references"]}

    main_tex = (PAPER / "main.tex").read_text(encoding="utf8")
    assert "\\documentclass[11pt]{article}" in main_tex
    packages = re.findall(r"\\usepackage(?:\[[^]]*\])?\{([^}]+)\}", main_tex)
    assert packages == ["amsmath,amssymb,amsthm,booktabs,hyperref,graphicx"]
    assert not re.search(r"(?<![A-Za-z0-9_])[A-Za-z]:[\\/]|file://", tex + bbl)
    for value in re.findall(r"\\(?:input|includegraphics)(?:\[[^]]*\])?\{([^}]+)\}", tex):
        assert not Path(value).is_absolute() and ".." not in Path(value).parts
    abstract = " ".join(re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}",
                                    main_tex, re.S).group(1).split())
    assert abstract == (PAPER / "abstract.txt").read_text(encoding="utf8").strip()
    assert len(abstract) <= 1900
    pdf = PdfReader(PAPER / "main.pdf")
    assert pdf.metadata["/Author"] == "Durand Serge"
    page_text = [page.extract_text() for page in pdf.pages]
    first_appendix = next(i + 1 for i, text in enumerate(page_text)
                          if "Generated Lean inventory" in text)
    main_pages = first_appendix - 1
    assert main_pages <= 30 and "Durand Serge" in page_text[0]
    assert "??" not in "\n".join(page_text)

    algebraic = strict(PAPER / "algebraic_inventory.json")
    analytic = strict(PAPER / "analytic_inventory.json")
    kinds = Counter(row["declaration_kind"] for row in algebraic["declarations"])
    assert kinds["theorem"] + kinds["lemma"] == algebraic["audited_result_count"] == 233
    degree_rows = algebraic["degree_data"]
    assert [row["N"] for row in degree_rows] == list(range(10, 61, 2))
    assert all(row["NS_minimum_Q"] == row["NS_minimum_Fp"] == row["alpha"] + 1
               for row in degree_rows)
    pc_rows = [row for row in degree_rows if row["PC_minimum_Fp"] is not None]
    assert len(pc_rows) == 14
    assert [row["PC_minimum_Fp"] for row in pc_rows[:11]] == [3,3,3,3,4,4,4,4,4,5,5]
    assert [row["PC_minimum_Fp"] for row in pc_rows[11:]] == [6,5,5]
    assert all(row["PC_minimum_Q"] is None for row in pc_rows[11:])
    assert all(row["PC_minimum_Q"] == row["PC_minimum_Fp"] for row in pc_rows[:11])
    assert analytic["extracted_axiom_audit_rows"]["total"] == len(analytic["declarations"]) == 1768
    assert analytic["recorded_official_counter"]["entries"] == 1488
    assert "not a count" in next(c["statement"] for c in claims if c["id"] == "A-INVENTORY-COUNTS")
    standard = {"propext", "Classical.choice", "Quot.sound"}
    for row in analytic["declarations"]:
        assert set(row["axioms"]) <= standard
    for row in algebraic["declarations"]:
        if row["axioms_used"] is not None:
            assert set(row["axioms_used"]) <= standard

    manual = [
        {"claim_ids": ["ALG-NS-LOWER", "ALG-NS-UPPER-LIMIT", "ALG-DEGREE-CURVES"],
         "finding": "Main text distinguishes the compiled universal necessary lower bound from finite equality at the measured points; no universal matching construction is asserted."},
        {"claim_ids": ["ALG-PC-HYPOTHESIS", "ALG-PC-ALPHA-GROUPING"],
         "finding": "KnapsackLowerBound remains explicit and conditional in Appendix B; alpha grouping is confined to fourteen finite-field measurements, with no larger-point rational transfer."},
        {"claim_ids": ["ALG-NO-ELIGIBLE-FAMILY", "ALG-COORDINATE-GUARDS", "ALG-UNIFORM-BERTRAND"],
         "finding": "The first-even data are EVIDENCE without Judge/Trophy promotion; coordinate pins remain distinct from whole-vector multiplicity; the composite-nine model is not called a SIEVE model."},
        {"claim_ids": ["A-PARTIAL-BATCHES", "A-GAMMA-CHAIN", "A-TRUNCATION-BOUNDARY"],
         "finding": "Partial global batches retain only the recorded passing modules; weighted Lambda tails and the full coefficient chain retain SOURCE/failed scope."},
        {"claim_ids": ["A-IBP", "A-OBSTRUCTION-SIGNED-GAP", "A-OBSTRUCTION-COST", "A-ARITHMETIC-OBSTRUCTIONS"],
         "finding": "The kernel boundary is retained; a norm envelope is not a signed lower bound; envelope cost and guarded finite obstructions do not exclude whole analytic methods."},
        {"claim_ids": ["A-NUMERICAL", "A-LOG", "R-THRESHOLD"],
         "finding": "The CRT/integer calculation has one-input scope; native and B40 real-log refinement are explicitly unproved; the interval to the stated analytic onset remains uncovered."},
        {"claim_ids": ["R-FROZEN", "R-PROTOCOL", "R-OUT-OF-SCOPE"],
         "finding": "The frozen proofless-file incompatibility is an acceptance-contract flaw; provider-shared reviews are not external validation; uncredited and axiomatic material receives no unconditional credit."}
    ]
    for check in manual:
        assert set(check["claim_ids"]) <= set(ids)
        check["status"] = "PASS: document scope matches existing mapped records"
    report = {"schema": "fresh-document-compile-claim-review-v1", "status": "PASS",
              "author": "Durand Serge", "scope": "Document compilation and claim-to-existing-evidence review only",
              "no_new_mathematical_execution_or_credit": True,
              "engine": compilation["engine"], "engine_version": compilation["engine_version"],
              "engine_basename": compilation["engine_basename"],
              "cached_resources_only": True, "untrusted_mode": True,
              "pdflatex_available": compilation["pdflatex_available"],
              "compile_exit_code": 0, "actual_bibtex_engine": "BibTeX 0.99d",
              "bibliography_style": "report.bst; transparent authored style, genuinely processed by BibTeX",
              "bibliography_entries": len(bibliography_keys), "unresolved_citations_or_references": 0,
              "overfull_boxes": 0, "main_text_pages": main_pages,
              "appendix_A_first_page": first_appendix, "total_pdf_pages": len(pdf.pages),
              "abstract_characters_excluding_terminal_newline": len(abstract),
              "claim_count": len(claims), "used_manuscript_evidence_keys": len(used),
              "unique_existing_source_bindings_checked": len(sources),
              "source_files": compilation["source_files"], "figure_files": compilation["figure_files"],
              "outputs": compilation["outputs"],
              "reviewed_metadata_bindings": {name: digest(PAPER / name) for name in
                  ["evidence_map.json", "analytic_inventory.json", "algebraic_inventory.json",
                   "analytic_lean_inventory.csv", "algebraic_lean_inventory.csv", "abstract.txt",
                   "bibliography_verification.json", "analytic_obstruction_catalogue.json"]},
              "manual_scope_checks": manual,
              "limitations": ["Actual pdflatex execution was unavailable; its compatibility was reviewed from standard source constructs but not executed.",
                              "The existing cached bundle lacked plain.bst and the default large-title OpenType font; portable Type1 settings and an authored BibTeX style were used without installation or network.",
                              "Underfull narrow-table spacing warnings remain; whole-document visual review is separate from this compilation and claim gate.",
                              "No mathematical experiments, Lean builds, certificate replays or provenance/credit audits were run.",
                              "Semantic review compares the manuscript to existing recorded statements; it is not external expert validation of their mathematics."]}
    (PAPER / "A6_COMPILE_CLAIM_REVIEW.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf8", newline="\n")
    print("A6 document review PASS:", len(pdf.pages), "PDF pages;", main_pages,
          "main pages;", len(abstract), "abstract characters;", len(claims), "mapped claims")


if __name__ == "__main__":
    main()
