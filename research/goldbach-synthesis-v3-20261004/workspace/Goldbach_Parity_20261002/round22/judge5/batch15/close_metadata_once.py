"""Close real AUX_PASS15 by metadata/rehash only; no compiler or model import."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch15_attempt01"


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
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH15_AUX_PASS"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
    assert receipt["modules_passed"] == 1 and receipt["declarations_passed"] == 29
    assert len(receipt["rows"]) == len(catalog["modules"]) == 1
    row = receipt["rows"][0]
    assert row["exit_code"] == 0 and not row["timed_out"] and row["launch_error"] is None
    assert read(ACTUAL / "DiscreteThermalProjection22_FIN.json") == row
    assert sha(ACTUAL / "DiscreteThermalProjection22.log") == row["log_sha256"] == "5a99f3e74a991301a707747540267ab38d0ea673b9ac5a53aed5f38359a1f0da"
    assert sha(ACTUAL / "DiscreteThermalProjection22.olean") == row["olean_sha256"] == "0835250ba8f951b5322f9fc4ffbdc5bde65c05be12e74b95a1873a7f6ca71546"
    assert sha(OWN / "sources/DiscreteThermalProjection22.lean") == row["source_sha256"] == "f24c702b0a6cd71e88ae1279061a45e02fa04f12f8e8641444d3b5e1803e8f02"
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 8060 and len(old["inputs"]) == 956 and len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 24
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == "bdd4f2eef9c52debe7222f73564c70ac40b6497ccbc313896a359f9553831f24"
    assert receipt["all_current_bytes_preserved"] and post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    assert receipt["readonly_local_dependencies"] == []
    log = (ACTUAL / "DiscreteThermalProjection22.log").read_text(encoding="utf-8")
    raw = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)
    audits = [{"declaration": name, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]} for name, values in raw]
    assert audits == row["axiom_rows"] and [r["declaration"] for r in audits] == catalog["modules"][0]["qualified_prints"]
    assert len(audits) == 29 and all(r["axioms"] == ["propext", "Classical.choice", "Quot.sound"] for r in audits)
    assert not re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", log)
    assert len(re.findall(r":\d+:\d+: error:", log)) == 0 and len(re.findall(r":\d+:\d+: warning:", log)) == 7
    empty = [r["declaration"] for r in audits if not r["axioms"]]
    names = ("START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json", "DiscreteThermalProjection22_START.json", "DiscreteThermalProjection22_FIN.json", "DiscreteThermalProjection22.log", "DiscreteThermalProjection22.olean")
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Lot15 clos : vrai AUX_PASS discret29

Unique invocation d35455/session93472→e7fa47 exit0 ; gate SHA{pre["gate_sha256"]} FULL113d1a, START préalable absent. Global START{start["time_utc"]} FIN{fin["time_utc"]} ; enfant START{row["started_at"]} FIN{row["finished_at"]}. Source révision03 SHA{row["source_sha256"]}, nouveau olean SHA{row["olean_sha256"]}. Aucun replay/retry/probe/ancien compilateur ou numérique. Log/reçu/START/FIN effectivement FULL652cc7, log SHA{row["log_sha256"]}.

Un module29=20 théorèmes9 définitions,29 prints exacts tous [propext,Classical.choice,Quot.sound], zéro sorryAx/erreur/axiome vide. Sept warnings unnecessarySeqFocus seulement. Les quatre raccords techniques du FAIL14 passent réellement ; l'ancien FAIL14 demeure clos séparément. Inventaire des noms et axiomes exacts dans catalog.json et reçu réel.

L'identité CIRCLE finie est acquise pour a réel quelconque, N≤M et A0 maxN(2M−N)<K. Racines exp explicites, géométrique finie, divisibilité signée et normalisation K/exp sont construits, sans orthogonalité finale supposée. Vraie somme Lambda(n)Lambda(N−n), y compris puissances premières. Cette projection paie le raccord discret de l'identité continue déjà acquise. Elle n'établit aucun programme natif NTT, catalogue/logs certifiés complets ou coefficient numérique calculé à10^8.

Conservation physiquement rehashée :8060inputs/956anciensJuge/3089archives/24captures et gate/source intacts ; PRE{links["PREEXEC.json"]["sha256"]}, POST{links["POSTEXEC.json"]["sha256"]}, reçu{links["receipt.json"]["sha256"]}. Grands JSON parsés intégralement et tous octets liés vérifiés, aucun rawFULL prétendu. Zéro dépendance locale/olean auteur, tous lots01–14 préservés. Baseline75/1223 ; proposition76/1252 uniquement après observation ROOT des29 nouveaux auxiliaires. H1/C5global, PP/frontière, D_N/Goldbach/WIN restent ouverts. Lot15 fermé, aucune préparation16 automatique.
'''
    new(OWN / "adjudication.md", report)
    completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH15", "time_utc": datetime.now(timezone.utc).isoformat(), "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 1, "declarations_passed": 29, "module_count_passed": 1, "declaration_count_passed": 29, "theorems_passed": 20, "definitions_passed": 9,
        "all_current_bytes_preserved": True, "all_inputs_unchanged": True, "input_count": 8060, "closed_judge_file_count": 956, "protected_archive_count": 3089, "capture_count": 24,
        "print_count": 29, "standard_print_count": 29, "recovery_sorryAx_print_count": 0, "declarations_without_axioms": empty, "warnings": 7, "errors": 0,
        "source_sha256": row["source_sha256"], "actual_links": links, "adjudication_sha256": sha(OWN / "adjudication.md"), "metadata_close_source_sha256": sha(Path(__file__)),
        "readonly_local_dependencies": [], "recompiled_dependencies": [], "old_batches_recompiled": False, "author_olean_used": False, "retry_count": 0,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False, "previous_official_modules": 75, "previous_official_declarations": 1223,
        "proposed_new_official_modules": 76, "proposed_new_official_declarations": 1252, "official_count_requires_ROOT_observation": True,
        "H1_paid": False, "C5_paid": False, "global_trace_certified": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False,
        "full_log_read": "652cc7", "full_actual_receipt_read": "652cc7", "full_START_read": "652cc7"}
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 1, "declarations_passed": 29, "all_current_bytes_preserved": True,
        "adjudication_sha256": sha(OWN / "adjudication.md"), "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))


if __name__ == "__main__":
    main()
