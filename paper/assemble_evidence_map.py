"""Assemble manuscript claim links from existing artifact-derived tables only.

Run from the repository root: python paper/assemble_evidence_map.py
No mathematical experiment, Lean execution, solver or Git operation is run.
"""
from pathlib import Path
import hashlib
import json
import math
import re

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
BASE_COMMIT = "f7e1fda19a9781b6f4ae6ebcae1dfc81b1b41460"
PUBLICATION = "publications/2026-10-goldbach-synthesis-v3-1"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def strict(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("Duplicate JSON key: " + key)
            result[key] = value
        return result
    def bad(value):
        raise ValueError(value)
    def finite(value):
        if isinstance(value, float) and not math.isfinite(value):
            raise ValueError("Nonfinite metadata")
        if isinstance(value, dict):
            for child in value.values():
                finite(child)
        elif isinstance(value, list):
            for child in value:
                finite(child)
    result = json.loads(path.read_text(encoding="utf8"), object_pairs_hook=unique, parse_constant=bad)
    finite(result)
    return result


def file_evidence(path, commit=None, locator=None):
    raw = (ROOT / path).read_bytes()
    result = {"path": path, "sha256": sha(raw), "bytes": len(raw)}
    if commit:
        result["commit"] = commit
    if locator:
        result["locator"] = locator
    return result


analytic = strict(PAPER / "analytic_claims.json")["claims"]
algebraic = strict(PAPER / "algebraic_claims.json")["claims"]
bibliography = strict(PAPER / "bibliography_verification.json")
claims = analytic + algebraic


def group_evidence(items):
    result = {}
    for item in items:
        for evidence in item["evidence"]:
            result[(evidence["path"], evidence["sha256"])] = evidence
    return list(result.values())


ae, ge = group_evidence(analytic), group_evidence(algebraic)
v3 = file_evidence(PUBLICATION + "/goldbach_synthesis_v3_1.tex", BASE_COMMIT)
scope = file_evidence("paper/scope_statement.json")
root_claims = [
    ("R-CORPORA", "The report consolidates the existing V3.1 analytic corpus and stopped algebraic campaign.", "Documentary", [v3] + ge),
    ("R-STOP", "The author stopped research and authorized only document consolidation, derived tables, compilation, claim review and an additive publication update.", "Author instruction", [scope]),
    ("R-PROTOCOL", "Evidence levels, standard axiom qualification and role separation have the scopes stated in section2; no external validation is implied.", "Verification protocol", ae + ge + [scope]),
    ("R-WINDOWS", "Historical raw/Git, newline and path-reader qualifications are documentary issues, distinct from mathematical replay.", "Documentary scope", ge),
    ("R-ATTRIBUTES", "The existing repository contains the requested LF text rule; no old file conversion is part of this update.", "Existing repository configuration", [file_evidence(".gitattributes", BASE_COMMIT), scope]),
    ("R-FROZEN", "The algebraic target is a bare unfinished frozen declaration, excluded from the auxiliary build; adding its proof changes its bytes.", "Source and acceptance-contract limitation", ge),
    ("R-ANALYTIC-GAP", "Exact coefficient identities and approximation radii do not supply the open signed reference-minus-coefficient estimate or erase its bridge conditions.", "Compiled identities and open obligation", ae + [v3]),
    ("R-BOUNDARY", "The credited integration-by-parts statement retains the actual kernel boundary term; it does not provide a favorable global sign.", "Compiled Lean, limited scope", ae),
    ("R-FEJER", "The existing written reconstruction/positive-definiteness discussion includes a restricted zero-coefficient example and no uniform prime-pair lower bound.", "PAPER", [v3] + ae),
    ("R-KERNEL", "The existing review reports a negative direction for one specific kernel restriction, not all operator methods.", "PAPER", [v3] + ae),
    ("R-ALGEBRAIC", "Calibrations, coordinate pins and family-specific common zeros have only their recorded domains and credit levels.", "Mixed compiled and finite evidence", ge),
    ("R-DEGREE", "Lean supplies the rational static NS lower bound; finite equality measurements do not establish a universal matching construction.", "Compiled lower bound and finite EVIDENCE", ge),
    ("R-PC", "The restriction corollary retains the explicit external KnapsackLowerBound predicate; finite PC observations do not discharge it.", "Conditional boundary and EVIDENCE", ge),
    ("R-NUMERICAL", "The existing integer/CRT computation concerns one input and does not certify a Lean native-program refinement or a global signed estimate.", "EVIDENCE", ae + [file_evidence(PUBLICATION + "/numerical_verdict.json", BASE_COMMIT)]),
    ("R-THRESHOLD", "The V3.1 analytic onset log(N)>=10^24 is not covered by its N=10^8 computation; published finite verification ends at4*10^18.", "Documented scope and verified literature", [v3, file_evidence("paper/bibliography_verification.json")]),
    ("R-REPRO", "Recorded repository/proof snapshots, Lean4.15.0, Mathlib9837ca9d and inventory/axiom sources are existing records, not a new Lean build.", "Reproducibility metadata", [file_evidence("lean-toolchain", BASE_COMMIT), file_evidence("lake-manifest.json", BASE_COMMIT)] + ge + ae),
    ("R-OUT-OF-SCOPE", "SOURCE-only links, the external PC predicate, unproved project axioms and non-Judge historical claims are not promoted into unconditional established results.", "Exclusion policy and recorded limits", [scope, file_evidence("audit/axiom_status_c5e3183.md", BASE_COMMIT)] + ae + ge),
    ("R-MSC", "The four requested MSC2020 codes and meanings were verified against the official classification.", "Verified bibliographic metadata", [file_evidence("paper/bibliography_verification.json")])
]
claims += [{"id": key, "statement": statement, "status": status, "evidence": evidence}
           for key, statement, status, evidence in root_claims]
for entry in bibliography["references"]:
    claims.append({"id": "BIB-" + entry["citekey"], "statement": entry["claim_scope"],
                   "status": entry["status"], "evidence": [file_evidence("paper/references.bib"),
                   file_evidence("paper/bibliography_verification.json")],
                   "verified_primary_sources": entry["sources"]})
ids = [claim["id"] for claim in claims]
assert len(ids) == len(set(ids)), "Duplicate claim identifiers"
all_sources = group_evidence(claims)
for evidence in all_sources:
    path = Path(evidence["path"])
    assert not path.is_absolute() and ".." not in path.parts
    raw = (ROOT / path).read_bytes()
    assert sha(raw) == evidence["sha256"], evidence["path"]
    if "bytes" in evidence:
        assert len(raw) == evidence["bytes"], evidence["path"]
text = "\n".join(path.read_text(encoding="utf8") for path in PAPER.glob("*.tex"))
used = {key for key in re.findall(r"\\(?:ev|evidence)\{([^{}]+)\}", text)
        if not re.fullmatch(r"#[1-9]", key)}
missing = used - set(ids)
assert not missing, "Unmapped manuscript evidence keys: " + repr(sorted(missing))
citekeys = set()
for citation in re.findall(r"\\cite\{([^{}]+)\}", text):
    citekeys.update(citation.split(","))
assert citekeys <= {entry["citekey"] for entry in bibliography["references"]}
inventories = [file_evidence("paper/analytic_inventory.json"), file_evidence("paper/analytic_lean_inventory.csv"),
               file_evidence("paper/algebraic_inventory.json"), file_evidence("paper/algebraic_lean_inventory.csv")]
result = {"schema":"negative-results-claim-evidence-map-v1", "author":"Durand Serge",
          "date":"2026-10-05", "purpose":"Portable claim-to-existing-evidence links; no new mathematical audit or credit",
          "repository_base_commit":BASE_COMMIT,
          "path_base":"repository root; all paths are portable and repository-relative",
          "historical_commit_vs_copied_bytes":"Original commits and copied raw SHA256 scopes are distinguished in source metadata; copied evidence is not a new mathematical run.",
          "claims":claims, "complete_inventory_artifacts":inventories,
          "all_used_manuscript_keys_mapped":True,
          "used_evidence_key_count":len(used),"source_file_count":len(all_sources),
          "all_citations_have_verified_bibliographic_entries":True}
(PAPER / "evidence_map.json").write_text(json.dumps(result,indent=2,ensure_ascii=True,allow_nan=False)+"\n",encoding="utf8",newline="\n")
print("Evidence map assembled", len(claims), "claims;", len(all_sources), "source files;",len(used),"used keys")
