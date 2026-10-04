"""Post-run documentary adjudication; no compiler or mathematical numeric invocation."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
OUT = OWN / "batch01_attempt01"


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def read(name):
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def write_new(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def main():
    pre, post, receipt, start = read("PREEXEC.json"), read("POSTEXEC.json"), read("receipt.json"), read("START.json")
    manifest_path = OWN / "batch01_prepared_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    catalog = json.loads((OWN / "batch01_catalog.json").read_text(encoding="utf-8"))
    if not (receipt["status"] == "INDEPENDENT_BATCH01_AUX_PASS"
            and receipt["actual_child_invocations"] == 2 and not receipt["hidden_retries"]
            and not receipt["author_olean_used"] and receipt["declarations_passed"] == 51
            and pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
            and pre["protected_archives"] == post["protected_archives"]
            and len(pre["protected_archives"]) == 3089
            and post["all_inputs_unchanged"] and post["gate_unchanged"]
            and sha(manifest_path) == pre["manifest_sha256"]
            and start["child_invocations_maximum"] == 2 and not start["hidden_retries"]):
        raise RuntimeError("Post-run receipt/metadata conservation mismatch")
    gate_path = Path(pre["gate_path"])
    if sha(gate_path) != pre["gate_sha256"] or post["gate_sha256"] != pre["gate_sha256"]:
        raise RuntimeError("Audit gate changed")
    captures = []
    for row in pre["captures"]:
        if sha(row["capture"]) != row["sha256"] or sha(row["source"]) != row["sha256"]:
            raise RuntimeError("Source/PREEXEC capture mismatch")
        captures.append(row)
    if len(captures) != 10:
        raise RuntimeError("Capture count mismatch")
    lean_paths = pre["LEAN_PATH"].split(";")
    if Path(lean_paths[0]).resolve() != OUT.resolve() or any("role3" in path or "role4" in path for path in lean_paths):
        raise RuntimeError("Author olean directory detected on audit LEAN_PATH")
    rows = []
    for actual, expected in zip(receipt["rows"], catalog["modules"]):
        module = expected["module"]
        source, log, olean = Path(expected["source"]), OUT / (module + ".log"), OUT / (module + ".olean")
        text = log.read_text(encoding="utf-8")
        matches = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S)
        names = [name for name, _ in matches]
        standard = {"propext", "Classical.choice", "Quot.sound"}
        allowed = all({item.strip() for item in values.replace("\n", " ").split(",") if item.strip()} <= standard
                      for _, values in matches)
        if (actual["module"] != module or actual["exit_code"] != 0
                or actual["status"] != "INDEPENDENT_LEAN_AUX_PASS"
                or names != expected["qualified_prints"] or not allowed
                or re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", text)
                or sha(source) != expected["source_sha256"] or sha(log) != actual["log_sha256"]
                or sha(olean) != actual["olean_sha256"]
                or not actual["exact_axiom_coverage_standard_only"]):
            raise RuntimeError("Independent module/axiom verification failed: " + module)
        fin = read(module + "_FIN.json")
        if fin != actual:
            raise RuntimeError("FIN and receipt disagree")
        rows.append({"module": module, "source_sha256": sha(source), "log_sha256": sha(log),
                     "olean_sha256": sha(olean), "started_at": actual["started_at"],
                     "finished_at": actual["finished_at"], "exit_code": actual["exit_code"],
                     "theorems": expected["theorem_count"], "definitions": expected["definition_count"],
                     "printed_axioms": len(matches), "standard_axioms_only": True,
                     "warning_count": len(re.findall(r"warning:", text)),
                     "source_and_log_FULL_reads": "c705ad/62d976; f59bfa/2c65c2"})
    verdict = {"schema": "ROUND22_JUDGE5_BATCH01_ADJUDICATION",
        "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": "INDEPENDENT_G0_KERNEL_FINITE_AUXILIARIES_CERTIFIED",
        "actual_launcher_invocation": "726a7e/session7993; final a1b533 exit0",
        "actual_compiler_invocations": 2, "hidden_retries": False,
        "independent_source_copies": True, "author_olean_used": False,
        "new_olean_hashes_may_equal_author_deterministically": True,
        "gate_sha256": sha(gate_path), "manifest_sha256": sha(manifest_path),
        "receipt_sha256": sha(OUT / "receipt.json"), "PREEXEC_sha256": sha(OUT / "PREEXEC.json"),
        "POSTEXEC_sha256": sha(OUT / "POSTEXEC.json"), "captures": captures,
        "immutable_inputs_conserved": len(pre["inputs"]), "protected_archives_conserved": 3089,
        "import_modules": manifest["import_module_count"], "rows": rows,
        "additional_audited_modules": 2, "additional_audited_declarations": 51,
        "theorem_count": 42, "definition_count": 9, "standard_axiom_prints": 51,
        "total_warning_count": sum(row["warning_count"] for row in rows),
        "read_scopes": {"receipt": "FULL0af772", "global_START": "FULL04488f",
                        "module_START": "FULLee2a74/b84ed3", "logs": "FULLf59bfa/2c65c2",
                        "PRE_POST_manifest": "Complete JSON parsed, compared and hashed; no FULL raw display",
                        "captures": "All10 source/capture byte hashes freshly checked; not FULL source display"},
        "certified_auxiliary_scope": ["Integrability and full real kernel mass", "Exact finite affine-cell unfolding"],
        "still_open": ["Infinite periodization and its tail", "Gamma strip bound and derivative",
                       "Weil trace identity with all arithmetic/archimedean terms",
                       "Complete certified nontrivial-zero boxes and count",
                       "Scattering/operator identification", "Global Goldbach coefficient and D_N ledger"],
        "full_continuous_contract_certified": False, "D_N_bound": False, "victory": False,
        "official_baseline_before_audit": {"modules": 57, "auxiliaries": 942},
        "official_totals_updated_by_judge": False, "post_audit_compiler_invocations": 0,
        "post_audit_mathematical_numeric_invocations": 0}
    write_new(OWN / "batch01_adjudication.json", verdict)
    print(json.dumps({"status": verdict["status"], "actual_compiler_invocations": 2,
                      "declarations": 51, "captures": len(captures),
                      "immutable_inputs_conserved": len(pre["inputs"]),
                      "protected_archives_conserved": 3089,
                      "adjudication_sha256": sha(OWN / "batch01_adjudication.json"),
                      "receipt_sha256": verdict["receipt_sha256"], "victory": False}))


if __name__ == "__main__":
    main()
