"""Post-run documentary adjudication only: no compiler or numerical mathematical run."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
OUT = OWN / "batch02_attempt01"
MODULES = ["EpsteinUnfold22", "EpsteinTail22", "GammaPrerequisites22"]
SOURCE_READS = ["b76d19", "529f97", "21d3da"]
LOG_READS = ["4ab11b", "2e1ebb", "c19f9e"]
START_READS = ["008794", "e69e17", "72a6c4"]
FIN_READS = ["7ef064", "e1a7e4", "33bdbb"]


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def write_new(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)


def main():
    pre, post = read(OUT / "PREEXEC.json"), read(OUT / "POSTEXEC.json")
    receipt, start = read(OUT / "receipt.json"), read(OUT / "START.json")
    manifest_path = OWN / "batch02_prepared_manifest.json"
    manifest, catalog = read(manifest_path), read(OWN / "batch02_catalog.json")
    require(receipt["status"] == "INDEPENDENT_BATCH02_AUX_PASS"
            and receipt["actual_child_invocations"] == 3
            and receipt["module_count_passed"] == 3 and receipt["declarations_passed"] == 56
            and not receipt["hidden_retries"] and not receipt["author_olean_used"]
            and not receipt["batch01_recompiled"] and not receipt["victory"]
            and not receipt["D_N_paid"] and not receipt["global_trace_certified"]
            and pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
            and len(pre["inputs"]) == 7214
            and pre["protected_archives"] == post["protected_archives"]
            and len(pre["protected_archives"]) == 3089
            and post["all_inputs_unchanged"] and receipt["all_inputs_unchanged"]
            and post["gate_unchanged"] and sha(manifest_path) == pre["manifest_sha256"]
            and start["modules"] == MODULES and start["child_invocations_maximum"] == 3
            and not start["hidden_retries"], "Closed batch receipt or conservation mismatch")
    gate_path = Path(pre["gate_path"])
    require(sha(gate_path) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"],
            "Audit gate changed")
    gate = read(gate_path)
    require(gate["authorized"] and gate["modules"] == MODULES and gate["no_win"]
            and gate["source_manifest_sha256"] == sha(manifest_path), "Gate scope mismatch")
    captures = []
    for row in pre["captures"]:
        require(sha(row["capture"]) == row["sha256"] == sha(row["source"]),
                "PREEXEC capture/source byte mismatch")
        captures.append(row)
    require(len(captures) == 23, "Capture count mismatch")
    paths = pre["LEAN_PATH"].split(";")
    require(len(paths) == 10 and Path(paths[0]).resolve() == OUT.resolve()
            and Path(paths[1]).resolve() == (OWN / "batch01_attempt01").resolve()
            and not pre["author_olean_in_lean_path"]
            and not any("role3" in p or "role4" in p for p in paths),
            "Author olean or unexpected local dependency on LEAN_PATH")
    old_bindings = read(OWN / "batch02_batch01_bindings.json")
    indexed_inputs = {row["path"]: row["sha256"] for row in pre["inputs"]}
    require(len(old_bindings["inputs"]) == 35 and not old_bindings["recompiled"],
            "Closed batch01 binding count mismatch")
    for row in old_bindings["inputs"]:
        require(indexed_inputs.get(row["path"]) == row["sha256"] == sha(row["path"]),
                "A closed batch01 file changed")
    require(read(OWN / "batch01_attempt01" / "receipt.json")["status"] ==
            "INDEPENDENT_BATCH01_AUX_PASS", "Old independent local dependency receipt changed")
    require([row["module"] for row in receipt["rows"]] == MODULES
            and [row["module"] for row in catalog["modules"]] == MODULES,
            "Independent compilation order or catalogue mismatch")
    rows = []
    for index, (actual, expected) in enumerate(zip(receipt["rows"], catalog["modules"])):
        module = expected["module"]
        source = Path(expected["source"])
        log, olean = OUT / (module + ".log"), OUT / (module + ".olean")
        text = log.read_text(encoding="utf-8")
        matches = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S)
        axioms = [{"declaration": name,
                   "axioms": [v.strip() for v in values.replace("\n", " ").split(",") if v.strip()]}
                  for name, values in matches]
        require(actual["status"] == "INDEPENDENT_LEAN_AUX_PASS" and actual["exit_code"] == 0
                and not actual["timed_out"] and actual["exact_axiom_coverage_standard_only"]
                and [name for name, _ in matches] == expected["qualified_prints"]
                and all(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
                        for row in axioms)
                and axioms == actual["axiom_rows"]
                and not re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", text)
                and not expected["source_forbidden_tokens"]
                and sha(source) == expected["source_sha256"] == actual["source_sha256"]
                and sha(log) == actual["log_sha256"] and sha(olean) == actual["olean_sha256"],
                "Independent module/source/axiom verification failed: " + module)
        module_start, fin = read(OUT / (module + "_START.json")), read(OUT / (module + "_FIN.json"))
        require(fin == actual and module_start["command"] == actual["command"]
                and module_start["child_invocations_maximum"] == 1
                and not module_start["hidden_retries"]
                and module_start["gate_sha256"] == pre["gate_sha256"],
                "Module START/FIN/receipt disagreement")
        rows.append({"module": module, "source_sha256": sha(source), "log_sha256": sha(log),
                     "olean_sha256": sha(olean), "START_marker": module_start["time_utc"],
                     "started_at": actual["started_at"], "finished_at": actual["finished_at"],
                     "exit_code": 0, "theorems": expected["theorem_count"],
                     "definitions": expected["definition_count"], "printed_axioms": len(axioms),
                     "standard_axioms_only": True, "warning_count": len(re.findall(r"warning:", text)),
                     "source_FULL_read": SOURCE_READS[index], "log_FULL_read": LOG_READS[index],
                     "START_FULL_read": START_READS[index], "FIN_FULL_read": FIN_READS[index],
                     "exact_axiom_rows": axioms})
    verdict = {
        "schema": "ROUND22_JUDGE5_BATCH02_ADJUDICATION",
        "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": "INDEPENDENT_UNFOLD_TAIL_GAMMA_AUXILIARIES_CERTIFIED",
        "actual_launcher_invocation": "cee27a/session37954; completion606534 exit0",
        "actual_compiler_invocations": 3, "hidden_retries": False,
        "independent_source_copies": True, "author_olean_used": False,
        "readonly_previous_judge_dependencies_only": ["EpsteinKernel22", "EpsteinFinite22"],
        "previous_batch_recompiled_or_replayed": False,
        "new_olean_hashes_may_equal_author_deterministically": True,
        "gate_sha256": sha(gate_path), "manifest_sha256": sha(manifest_path),
        "receipt_sha256": sha(OUT / "receipt.json"), "PREEXEC_sha256": sha(OUT / "PREEXEC.json"),
        "POSTEXEC_sha256": sha(OUT / "POSTEXEC.json"), "captures": captures,
        "immutable_inputs_conserved": 7214, "protected_archives_conserved": 3089,
        "closed_batch01_files_conserved": 35, "import_modules": 3568, "rows": rows,
        "additional_audited_modules": 3, "additional_audited_declarations": 56,
        "theorem_count": 47, "definition_count": 9, "standard_axiom_prints": 56,
        "total_warning_count": sum(row["warning_count"] for row in rows),
        "read_scopes": {
            "gate": "FULL464a37", "receipt": "FULLfeeb00", "global_START": "FULL8536d0",
            "module_logs": "FULL4ab11b/2e1ebb/c19f9e",
            "module_START": "FULL008794/e69e17/72a6c4",
            "module_FIN": "FULL7ef064/e1a7e4/33bdbb",
            "PRE_POST_manifest": "Complete JSON parsed, compared and hashed; header projection ccbef7; no FULL raw display",
            "captures": "All23 source/capture bytes freshly hashed; no claim of FULL rendered source display",
            "closed_batch01_files": "All35 bytes freshly compared to frozen bindings; no execution",
            "numeric_banks": "Closed existing result status/case projections only; no replay or new numeric certificate verification"
        },
        "certified_auxiliary_scope": [
            "Actual summable periodization, signed integer m unfolding, and integral/series interchange",
            "Actual infinite-minus-finite error with explicit bound and jointly continuous real envelope",
            "Actual Complex.Gamma Laplace integrability, analytic identity, rotation and unit-strip exponential norm bound"
        ],
        "premises_audit": "Auxiliary hypotheses are positivity/domain/nonzero/truncation constraints. Summability, integrability, domination and analyticity used in these conclusions are derived. No free Weil, zero-count, scattering, coefficientN or D_N target premise supplies these conclusions.",
        "still_open": ["H1 Mellin/Euler/logarithmic derivative and infinite contour passage",
                       "Gamma logarithmic derivative and weighted archimedean trace terms",
                       "Weil trace identity with every arithmetic and archimedean term",
                       "Complete certified nontrivial-zero boxes and count",
                       "Scattering/operator identification and full global m sum",
                       "Global Goldbach coefficient and D_N ledger"],
        "full_continuous_contract_certified": False, "D_N_bound": False, "victory": False,
        "official_baseline_before_audit": {"modules": 59, "auxiliary_declarations": 993},
        "proposed_totals_after_root_observation": {"modules": 62, "auxiliary_declarations": 1049},
        "official_totals_updated_by_judge": False,
        "post_audit_compiler_invocations": 0, "post_audit_mathematical_numeric_invocations": 0
    }
    write_new(OWN / "batch02_adjudication.json", verdict)
    print(json.dumps({"status": verdict["status"], "actual_compiler_invocations": 3,
                      "declarations": 56, "captures": 23, "immutable_inputs_conserved": 7214,
                      "protected_archives_conserved": 3089, "closed_batch01_files_conserved": 35,
                      "adjudication_sha256": sha(OWN / "batch02_adjudication.json"),
                      "receipt_sha256": verdict["receipt_sha256"], "victory": False}))


if __name__ == "__main__":
    main()
