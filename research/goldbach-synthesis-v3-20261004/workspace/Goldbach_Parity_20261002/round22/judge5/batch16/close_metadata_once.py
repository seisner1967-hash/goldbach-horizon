"""Close the one real FAIL16: hashing/log metadata only, no candidate import."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch16_attempt01"

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))

def new(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(value)

def main():
    assert not (OWN / "adjudication.md").exists() and not (OWN / "completion_receipt.json").exists()
    receipt, pre, post, start, fin = [read(ACTUAL / name) for name in ("receipt.json", "PREEXEC.json", "POSTEXEC.json", "START.json", "FIN.json")]
    catalog, manifest, old = [read(OWN / name) for name in ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json")]
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH16_FAILED"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == len(receipt["rows"]) == 1
    assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
    assert len(catalog["modules"]) == 2 and catalog["total_declarations"] == 52
    row = receipt["rows"][0]
    assert row["module"] == "RationalLogQuantization22" and row["exit_code"] == 1
    assert not row["timed_out"] and row["launch_error"] is None and row["olean_sha256"] is None
    assert read(ACTUAL / "RationalLogQuantization22_FIN.json") == row
    assert sha(ACTUAL / "RationalLogQuantization22.log") == row["log_sha256"] == "45311354041cb407df0372b3f764bdb2bf90ea66b0a3100b1b072945510ef5c6"
    assert sha(OWN / "sources/RationalLogQuantization22.lean") == row["source_sha256"] == "9e59eb6b8aa4efcb5cc6cdc27d7d7a7d24517986fcd1ad2b4413b97c0efc1fb0"
    assert not list(ACTUAL.glob("*.olean"))
    assert not list(ACTUAL.glob("QuantizedLambdaEnvelope22*"))
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 8112 and len(old["inputs"]) == 1006 and len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 23
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == "32b5877b8a36c6cf2904b837d0c4a25adb2da213690825446499316b42016a87"
    assert receipt["all_current_bytes_preserved"] and post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    assert receipt["readonly_local_dependencies"] == []
    log = (ACTUAL / "RationalLogQuantization22.log").read_text(encoding="utf-8")
    raw = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)
    audits = [{"declaration": name, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]} for name, values in raw]
    assert audits == row["axiom_rows"] and [r["declaration"] for r in audits] == catalog["modules"][0]["qualified_prints"]
    standard = [r for r in audits if set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}]
    recovery = [r for r in audits if "sorryAx" in r["axioms"]]
    empty = [r["declaration"] for r in audits if not r["axioms"]]
    assert len(audits) == 38 and len(standard) == 29 and len(recovery) == 9
    assert empty == ["GoldbachLogQuantization22.clampInteger"]
    assert len(re.findall(r":\d+:\d+: error:", log)) == 4 and len(re.findall(r":\d+:\d+: warning:", log)) == 4
    names = ("START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json", "RationalLogQuantization22_START.json", "RationalLogQuantization22_FIN.json", "RationalLogQuantization22.log")
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Lot 16 clos : FAIL technique, zéro crédit

Une seule invocation réelle 873df7/session84428→b25998 exit1 ; gate FULLacd262 SHA {pre["gate_sha256"]}, START préalable absent. Global START {start["time_utc"]}, FIN {fin["time_utc"]} ; Rational START {row["started_at"]}, FIN {row["finished_at"]}, exit1, pas d'olean. Envelope14 NON_INVOKED conformément à stopfirstfail. Aucun retry/probe/ancien compilateur/numérique. Source 9e59eb6b… immuable, log SHA {row["log_sha256"]} FULL9acef7 ; receipt/START/FIN FULL3f0ffa.

Quatre diagnostics réellement imposés par Lean : ligne70, normalisation de logTerm avec la série API (coefficient inverse) non résolue par simpa ; lignes151 et190, exact_mod_cast ne transporte pas l'inégalité rationnelle reducedArg≤1/3 vers ℝ ; ligne236, conversion de l'erreur rationnelle nearestEven/abs vers ℝ non résolue. Ce sont des raccords de types et simplification. Aucun déficit analytique, constante insuffisante ou obstruction de parité n'est déduit de ces erreurs. Les énoncés SOURCE restent ceux déjà audités ; toute réparation doit être une révision distincte sous nouvelle sélection/gate, aucun replay de ce lot.

38 prints exacts en ordre :29 standard-only dont clampInteger sans aucun axiome, et9 contenant sorryAx de recovery. Ces29 prints ne constituent aucun crédit partiel de module : exit1/pasolean/coverage standard-only false. Le second module14 n'a ni START/log/FIN/olean. Inventaire exact dans catalogue et reçu réel ; zéro nouveau module ou déclaration acquis.

Conservation physiquement rehashée :8112inputs/1006 anciens Juge/3089archives/23captures et gate intacts. PRE {links["PREEXEC.json"]["sha256"]}, POST {links["POSTEXEC.json"]["sha256"]}, receipt {links["receipt.json"]["sha256"]}. Grands JSON parsés et tous octets liés vérifiés, sans prétendre rawFULL du texte des imports. Les lots01–15 restent clos readonly. Baseline officielle76/1252 inchangée. Pont natif/canonical32 exécuté, coefficientN à10^8, H1global/C5global, PP/frontière/D_N/Goldbach/WIN restent ouverts. Aucun nouveau lot automatiquement préparé.
'''
    new(OWN / "adjudication.md", report)
    completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH16", "time_utc": datetime.now(timezone.utc).isoformat(), "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 0, "declarations_passed": 0, "module_count_passed": 0, "declaration_count_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
        "all_current_bytes_preserved": True, "all_inputs_unchanged": True, "input_count": 8112, "closed_judge_file_count": 1006, "protected_archive_count": 3089, "capture_count": 23,
        "print_count": 38, "standard_print_count": 29, "recovery_sorryAx_print_count": 9, "declarations_without_axioms": empty, "warnings": 4, "errors": 4,
        "passed_modules": [], "failed_modules": [row["module"]], "not_invoked_modules": ["QuantizedLambdaEnvelope22"],
        "source_sha256": row["source_sha256"], "actual_links": links, "adjudication_sha256": sha(OWN / "adjudication.md"), "metadata_close_source_sha256": sha(Path(__file__)),
        "readonly_local_dependencies": [], "recompiled_dependencies": [], "old_batches_recompiled": False, "author_olean_used": False, "retry_count": 0,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False, "previous_official_modules": 76, "previous_official_declarations": 1252,
        "proposed_new_official_modules": 76, "proposed_new_official_declarations": 1252, "official_count_requires_ROOT_observation": True,
        "H1_paid": False, "C5_paid": False, "global_trace_certified": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False,
        "full_log_read": "9acef7", "full_actual_receipt_read": "3f0ffa", "full_START_read": "3f0ffa"}
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 0, "declarations_passed": 0, "all_current_bytes_preserved": True,
        "adjudication_sha256": sha(OWN / "adjudication.md"), "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))

if __name__ == "__main__":
    main()
