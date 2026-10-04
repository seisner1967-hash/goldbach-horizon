"""Close this real failed batch once, with physical SHA checks only; no subprocess/import of candidates."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch12_attempt01"

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))

def new(path, text):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)

def main():
    receipt = read(ACTUAL / "receipt.json")
    pre = read(ACTUAL / "PREEXEC.json")
    post = read(ACTUAL / "POSTEXEC.json")
    start = read(ACTUAL / "START.json")
    fin = read(ACTUAL / "FIN.json")
    catalog = read(OWN / "catalog.json")
    old = read(OWN / "closed_judge_bindings.json")
    manifest = read(OWN / "prepared_manifest.json")
    row = receipt["rows"][0]
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH12_FAILED"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
    assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
    assert row["module"] == "ThermalProjectionIdentity22" and row["exit_code"] == 1
    assert row["olean_sha256"] is None and not (ACTUAL / "ThermalProjectionIdentity22.olean").exists()
    assert row["log_sha256"] == "f4cdc3f9f0ed4922a320a43230c5299e9c6319f065aff55ea5881d994eb01501"
    assert sha(ACTUAL / "ThermalProjectionIdentity22.log") == row["log_sha256"]
    assert row["source_sha256"] == "533f81f523f465240ebf7f129d32c9d6c0119e0e0d7936a42bc65e75823880d0"
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 7951 and len(old["inputs"]) == 815
    assert len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 23
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"]
    assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    assert receipt["all_inputs_unchanged"] and receipt["all_current_bytes_preserved"]
    text = (ACTUAL / "ThermalProjectionIdentity22.log").read_text(encoding="utf-8")
    raw = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", text, re.S)
    audits = [{"declaration": name, "axioms": [value.strip() for value in (values or "").replace("\n", " ").split(",") if value.strip()]} for name, values in raw]
    assert audits == row["axiom_rows"]
    assert [item["declaration"] for item in audits] == catalog["modules"][0]["qualified_prints"]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    standard = [item["declaration"] for item in audits if set(item["axioms"]) <= allowed]
    recovery = [item["declaration"] for item in audits if "sorryAx" in item["axioms"]]
    empty = [item["declaration"] for item in audits if not item["axioms"]]
    assert len(audits) == 20 and len(standard) == 13 and len(recovery) == 7 and not empty
    assert len(re.findall(r":\d+:\d+: error:", text)) == 1
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in (
        "START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json",
        "ThermalProjectionIdentity22_START.json", "ThermalProjectionIdentity22_FIN.json", "ThermalProjectionIdentity22.log")}
    report = f'''# Juge indépendant — lot12 clos, FAIL technique

Une seule tentative réelle :3632e1/session73190→928276 exit1. Gate6aa2f7ca4cacb3cadc6bd25ce6a9e84634629fe98700cfbaf0c22314f14f4a8e lue FULL5cc73d. Global START {start["time_utc"]}, FIN {fin["time_utc"]}. Identity START {row["started_at"]}, FIN {row["finished_at"]}, exit1, aucun olean. Status exact {receipt["status"]}. Zéro module et zéro déclaration crédités ; aucune reprise.

Source533f81f523f465240ebf7f129d32c9d6c0119e0e0d7936a42bc65e75823880d0 immuable. Un seul diagnostic43:2 dans la branche k≠0 : hperiod écrit exp(↑k*I*↑(2*pi))=1 ; le but après la vraie intégrale globale écrit exp(↑k*I*(2*↑pi))−1=0. La coercition réelle du produit doit être normalisée dans hperiod avant le simp final. Il s'agit d'un raccord syntaxique des casts dans deux expressions mathématiquement égales. Le log ne montre ni contradiction analytique ni obstruction de parité. Les trois autres réparations (map_neg, sum_comm et réduction lambda) n'émettent plus d'erreur. Les trois warnings concernent unnecessarySeqFocus uniquement. Diagnostic précis transmis à ROLE4 pour une éventuelle nouvelle SOURCE distincte sous sélection ROOT ; aucun essai implicite de réparation.

Log FULL376893, SHA{row["log_sha256"]}. Reçu/START/FIN FULL538a73. Les vingt audits sont présents dans l'ordre exact :13standards et7 contenant recovery sorryAx, aucune déclaration sans axiomes. Tous les noms et listes exactes figurent dans le log et le reçu ; les7recovery dépendent de integral_signedCircleCharacter. Aucun crédit partiel malgré les13audits standards, aucun sorry écrit dans la SOURCE, absence d'olean. Les audits dépendants sont : {", ".join(recovery)}.

Conservation physiquement revérifiée par close_metadata_once.py :7951inputs,815anciensJuge,3089archives,23captures, gate et source courante inchangés. PRE SHA{links["PREEXEC.json"]["sha256"]}, POST SHA{links["POSTEXEC.json"]["sha256"]}, reçu SHA{links["receipt.json"]["sha256"]}. Les gros PRE/POST sont lus intégralement par le checker metadata, tous octets vérifiés ; aucune lecture rawFULL de leur texte n'est prétendue. Envelope PASS11 source77cd/olean9c2bb947 est readonly et n'a pas été recompilé. Aucun olean auteur, ancien lot, probe, test numérique ou banc rejoué.

La revue SOURCE avait vérifié vraieΛ/PP, normalisation, convergence uniforme et intégrabilité construite sous a>0, sans finale prémisse. Ces obligations d'Identity restent sans crédit compiler. Envelope42 demeure l'acquis indépendant précédent. Baseline officielle avant nouvelle observation ROOT :74modules/1203auxiliaires, aucune augmentation proposée. Aucun producteur spectral uniforme, coefficient numérique à10^8, H1/C5global, frontière/D_N/Goldbach/WIN acquis. Ce lot est fermé immuable.
'''
    new(OWN / "adjudication.md", report)
    completion = {
        "schema": "ROUND22_JUDGE5_COMPLETION_BATCH12", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 0, "declarations_passed": 0, "module_count_passed": 0, "declaration_count_passed": 0,
        "theorems_passed": 0, "definitions_passed": 0, "all_current_bytes_preserved": True,
        "all_inputs_unchanged": True, "input_count": 7951, "closed_judge_file_count": 815,
        "protected_archive_count": 3089, "capture_count": 23, "print_count": 20,
        "standard_print_count_in_failed_module": 13, "recovery_sorryAx_print_count": 7,
        "declarations_without_axioms": empty, "partial_credit_in_failed_module": 0,
        "source_sha256": row["source_sha256"], "actual_links": links,
        "adjudication_sha256": sha(OWN / "adjudication.md"), "metadata_close_source_sha256": sha(Path(__file__)),
        "readonly_local_dependencies": ["ThermalProjectionEnvelope22"], "recompiled_dependencies": [],
        "failure_class": "TECHNICAL_CAST_NORMALIZATION_ONE_GOAL", "analytic_counterexample_observed": False,
        "parity_obstruction_observed": False, "old_batches_recompiled": False, "author_olean_used": False,
        "retry_count": 0, "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "previous_official_modules": 74, "previous_official_declarations": 1203,
        "proposed_new_official_modules": 74, "proposed_new_official_declarations": 1203,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C5_paid": False,
        "global_trace_certified": False, "D_N_paid": False, "WIN": False,
        "full_log_read": "376893", "full_actual_receipt_read": "538a73"
    }
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 0, "declarations_passed": 0,
        "all_current_bytes_preserved": True, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))

if __name__ == "__main__":
    main()
