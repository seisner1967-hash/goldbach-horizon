"""Close FAIL14 once by rehashing immutable files and parsing real logs; no subprocess."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch14_attempt01"

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
    assert not (OWN / "adjudication.md").exists() and not (OWN / "completion_receipt.json").exists()
    receipt, pre, post = (read(ACTUAL / name) for name in ("receipt.json", "PREEXEC.json", "POSTEXEC.json"))
    start, fin = read(ACTUAL / "START.json"), read(ACTUAL / "FIN.json")
    catalog, manifest, old = (read(OWN / name) for name in ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json"))
    assert len(receipt["rows"]) == len(catalog["modules"]) == 1
    row = receipt["rows"][0]
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH14_FAILED"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
    assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
    assert row["module"] == "DiscreteThermalProjection22" and row["exit_code"] == 1
    assert not row["timed_out"] and row["launch_error"] is None
    assert row["olean_sha256"] is None and not (ACTUAL / "DiscreteThermalProjection22.olean").exists()
    assert sha(ACTUAL / "DiscreteThermalProjection22.log") == row["log_sha256"] == "879f2978a6de8935608661b3194a36c728fbff743c864c3f114405fc463c3d0a"
    assert sha(OWN / "sources/DiscreteThermalProjection22.lean") == row["source_sha256"] == "7ee2abb27d959f1511abb59e8425578b420d3e972a8d03eaff26635ac8fd581c"
    assert read(ACTUAL / "DiscreteThermalProjection22_FIN.json") == row
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 8015 and len(old["inputs"]) == 911
    assert len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 20
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == "324a93bc75810a449a18b383294d8b7cd688091d01ae114c47be9b11f2b772c4"
    assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    assert receipt["all_inputs_unchanged"] and receipt["all_current_bytes_preserved"]
    assert receipt["readonly_local_dependencies"] == []
    log = (ACTUAL / "DiscreteThermalProjection22.log").read_text(encoding="utf-8")
    raw = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)
    audits = [{"declaration": name, "axioms": [word.strip() for word in (values or "").replace("\n", " ").split(",") if word.strip()]} for name, values in raw]
    assert audits == row["axiom_rows"]
    assert [item["declaration"] for item in audits] == catalog["modules"][0]["qualified_prints"]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    standard = [item["declaration"] for item in audits if set(item["axioms"]) <= allowed]
    recovery = [item["declaration"] for item in audits if "sorryAx" in item["axioms"]]
    empty = [item["declaration"] for item in audits if not item["axioms"]]
    assert len(audits) == 29 and len(standard) == 22 and len(recovery) == 7 and not empty
    assert len(re.findall(r":\d+:\d+: error:", log)) == 4 and len(re.findall(r":\d+:\d+: warning:", log)) == 6
    names = ("START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json",
        "DiscreteThermalProjection22_START.json", "DiscreteThermalProjection22_FIN.json", "DiscreteThermalProjection22.log")
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Lot14 indépendant clos : FAIL technique, zéro crédit

Une invocation 94511f/session12587→a122c1 exit1, gate {pre["gate_sha256"]} FULL3601b1, aucun START préalable. Global START {start["time_utc"]}, FIN {fin["time_utc"]}. Discret29 START {row["started_at"]}, FIN {row["finished_at"]}. Source revision02 {row["source_sha256"]} immuable, aucun olean, aucun crédit partiel, aucune reprise.

Quatre erreurs réelles, log FULL8a6633 SHA{row["log_sha256"]} :92:28 et114:6, rw sous ite produit un motive invalide car Decidable dépend de la proposition réécrite ;196:2, push_cast normalise exp et quotient dans hc mais le but conserve le cast réel du quotient ;285:2, h conserve le cast d'une négation entière et le but porte une négation complexe. Ce sont des raccords de tactiques/coercions, pas des contre-exemples mathématiques ou une obstruction de parité. La racine primitive, la période signée et l'expansion sum_mul_sum révisée n'émettent pas d'erreur. Six warnings unnecessarySeqFocus seulement. Les diagnostics précis ont été transmis à ROLE3 et ROOT pour une éventuelle révision SOURCE distincte sous sélection/gate nouvelles.

29 prints exacts :22 standards,7 recovery sorryAx, aucune déclaration sans axiomes. Les sept noms contaminés sont {", ".join(recovery)}. Leur présence n'est ni un sorry écrit dans la source ni une preuve admissible ; le module entier reçoit zéro crédit. Reçu/FIN FULLbc32b7 ; START global/module FULL2f0ae7. Le catalogue29 et la revue SOURCE demeurent préalables sans PASS.

Conservation physiquement revérifiée :8015 inputs,911 anciens fichiers Juge,3089 archives,20 captures et gate/source actuelles intacts. PRE SHA{links["PREEXEC.json"]["sha256"]}, POST SHA{links["POSTEXEC.json"]["sha256"]}, reçu SHA{links["receipt.json"]["sha256"]}. Gros JSON parsés intégralement et fichiers liés hachés ; aucun rawFULL des grands manifestes prétendu. Zéro dépendance locale, olean auteur, ancien module recompilé, retry, probe ou calcul numérique. Les lots01–13 restent préservés.

Baseline officielle inchangée :75 modules/1223 auxiliaires avant observation ROOT du FAIL14. Le contrat discret reste mathématiquement motivé sur papier, mais CIRCLE29 ne reçoit pas de crédit compilateur. L'identité CONTINUE20 et l'enveloppe42 déjà PASS restent acquis sans recompilation. Le coefficient numérique à10^8, log/NTT/certificats effectifs, H1/C5global, PP/frontière/D_N/Goldbach/WIN ne sont pas acquittés. Lot14 fermé ; aucune préparation15 automatique.
'''
    new(OWN / "adjudication.md", report)
    completion = {
        "schema": "ROUND22_JUDGE5_COMPLETION_BATCH14", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 0, "declarations_passed": 0, "module_count_passed": 0, "declaration_count_passed": 0,
        "theorems_passed": 0, "definitions_passed": 0, "all_current_bytes_preserved": True, "all_inputs_unchanged": True,
        "input_count": 8015, "closed_judge_file_count": 911, "protected_archive_count": 3089, "capture_count": 20,
        "print_count": 29, "standard_print_count_in_failed_module": 22, "recovery_sorryAx_print_count": 7,
        "declarations_without_axioms": empty, "partial_credit_in_failed_module": 0, "source_sha256": row["source_sha256"],
        "actual_links": links, "adjudication_sha256": sha(OWN / "adjudication.md"), "metadata_close_source_sha256": sha(Path(__file__)),
        "readonly_local_dependencies": [], "recompiled_dependencies": [], "failure_class": "TECHNICAL_ITE_DEPENDENT_DECIDABLE_AND_CAST_NORMALIZATIONS",
        "analytic_counterexample_observed": False, "parity_obstruction_observed": False, "old_batches_recompiled": False,
        "author_olean_used": False, "retry_count": 0, "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "previous_official_modules": 75, "previous_official_declarations": 1223,
        "proposed_new_official_modules": 75, "proposed_new_official_declarations": 1223,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C5_paid": False,
        "global_trace_certified": False, "D_N_paid": False, "WIN": False,
        "full_log_read": "8a6633", "full_actual_receipt_read": "bc32b7", "full_START_read": "2f0ae7"
    }
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 0, "declarations_passed": 0,
        "all_current_bytes_preserved": True, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))

if __name__ == "__main__":
    main()
