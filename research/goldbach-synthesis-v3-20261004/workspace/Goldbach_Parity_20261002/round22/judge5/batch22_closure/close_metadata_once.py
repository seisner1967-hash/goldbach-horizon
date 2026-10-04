"""Documentary closure of actual22 only; no compiler, candidate import or calculation."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch22"
A = P / "batch22_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch22_authorization.json"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = ["ConcreteNTTRoots22", "ConcreteNTTA32Projection22"]

def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))

def checked(path, expected):
    assert sha(path) == expected, str(path)

def write_new(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(value)

assert not (P / "adjudication.md").exists()
assert not (P / "completion_receipt.json").exists()
receipt, pre, post = (read(A / name) for name in ("receipt.json", "PREEXEC.json", "POSTEXEC.json"))
catalog = read(P / "catalog.json")
manifest = read(P / "prepared_manifest.json")
old = read(P / "closed_judge_bindings.json")
fin, start = read(A / "FIN.json"), read(A / "START.json")
gate = read(G)
assert gate["authorized"] is True and gate["attempt"] == "batch22_attempt01"
assert gate["modules"] == EXPECTED and gate["compiler_invocations_maximum"] == 2
checked(G, "ceb0edb6fe964e10f25d7bf09c2bfbfc553c1f609db7d79ae70d0f928818baec")
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH22_AUX_PASS"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 2
assert receipt["modules_passed"] == 2 and receipt["declarations_passed"] == 28
assert all(receipt[k] is False for k in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"]
assert pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 8441
assert len(pre["captures"]) == receipt["capture_count"] == 95
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 1330
for row in pre["inputs"]:
    checked(row["path"], row["sha256"])
for row in old["inputs"]:
    checked(row["path"], row["sha256"])
for row in pre["protected_archives"]:
    path = Path(row["path"])
    checked(path if path.is_absolute() else B / path, row["sha256"])
for row in pre["captures"]:
    checked(row["source"], row["sha256"])
    checked(row["capture"], row["sha256"])
all_axioms = []
module_evidence = []
assert [row["module"] for row in receipt["rows"]] == EXPECTED
for result, module in zip(receipt["rows"], catalog["modules"]):
    name = result["module"]
    assert name == module["module"]
    assert result["exit_code"] == 0 and not result["timed_out"] and result["launch_error"] is None
    assert result["status"] == "INDEPENDENT_LEAN_AUX_PASS"
    checked(module["source"], result["source_sha256"])
    checked(module["original_source"], result["source_sha256"])
    checked(A / (name + ".log"), result["log_sha256"])
    checked(A / (name + ".olean"), result["olean_sha256"])
    text = (A / (name + ".log")).read_text(encoding="utf-8-sig")
    assert not re.search(r"\b(?:error|warning|sorryAx|native_decide|ofReduceBool)\b", text)
    rows = [{"declaration": n, "axioms": [v.strip() for v in values.split(",") if v.strip()]}
            for n, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)]
    assert rows == result["axiom_rows"]
    assert [row["declaration"] for row in rows] == module["qualified_prints"]
    assert len(rows) == len(module["declarations"])
    assert all(set(row["axioms"]) <= STANDARD for row in rows)
    mf = read(A / (name + "_FIN.json"))
    ms = read(A / (name + "_START.json"))
    assert mf == result and ms["time_utc"] == result["started_at"]
    all_axioms.extend(rows)
    module_evidence.append({"module": name, "started_at": result["started_at"], "finished_at": result["finished_at"],
                            "exit_code": 0, "declarations_passed": len(rows),
                            "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"],
                            "olean_sha256": result["olean_sha256"]})
assert len(all_axioms) == 28 and catalog["theorem_count"] == 22 and catalog["definition_count"] == 6
counts = {"standard_triplet": sum(set(r["axioms"]) == STANDARD for r in all_axioms),
          "propext_Quot_sound": sum(set(r["axioms"]) == {"propext", "Quot.sound"} for r in all_axioms),
          "empty": sum(not r["axioms"] for r in all_axioms), "recovery": 0}
assert counts == {"standard_triplet": 27, "propext_Quot_sound": 1, "empty": 0, "recovery": 0}
now = datetime.now(timezone.utc).isoformat()
lines = ["# Adjudication indépendante — lot22", "", "Statut réel : INDEPENDENT_BATCH22_AUX_PASS.", "",
         f"L'unique tentative batch22_attempt01 a invoqué deux enfants Lean, sans reprise : START {start['time_utc']}, FIN {fin['time_utc']}.",
         "Roots révision02 puis Bridge inchangé : deux exit0, deux oleans indépendants, 28 déclarations auxiliaires (22 théorèmes, 6 définitions).", "",
         "Les 28 noms imprimés correspondent exactement au catalogue : 27 listes [propext, Classical.choice, Quot.sound] ; bankRoot utilise [propext, Quot.sound]. Aucune liste vide, aucun sorryAx, aucun axiome personnalisé/native, aucune erreur ou alerte dans les deux logs.", "",
         "Les cinq primalités sont établies par les obligations Lucas concrètes et les cinq ordres primitifs 2^27 par les puissances whole/half effectives dans Lean. Les coercions Nat→ZMod et la réduction de val ont effectivement été élaborées. Le Bridge construit les cinq Fact et spécialise la projection finie A32 précédemment démontrée ; ni primalité ni racine ne sont une prémisse offerte.", "",
         "La projection porte sur les poids canoniques A32 et conserve les puissances premières. Les butterflies DIT/DIF, le raffinement GMP/CRT, le calcul effectif du coefficient N=10^8, le passage à la corrélation spectrale globale et la cible D_N restent distincts et ouverts. Aucun H1/C5 global ni WIN n'est accordé.", "",
         "Conservation physique après FIN : 8441 entrées, 1330 anciens fichiers (incluant le lot21 ROLE4 clos), 3089 archives et 95 captures original/copie, tous rehashés sans changement ; gate et inputs PRE/POST concordent. Trois oleans indépendants19/17 readonly ; aucun olean auteur, aucune ancienne compilation, aucun banc numérique ou exécutable natif invoqué.", "",
         "La baseline officielle demeure 80 modules/1339 déclarations jusqu'à l'observation ROOT ; 82/1367 est uniquement le total potentiel après son crédit de deux modules entiers.", "",
         f"Reçu réel : {A / 'receipt.json'} ; SHA256 {sha(A / 'receipt.json')}.",
         f"PREEXEC : {sha(A / 'PREEXEC.json')} ; POSTEXEC : {sha(A / 'POSTEXEC.json')}.", ""]
for item in module_evidence:
    lines.extend([f"- {item['module']} : {item['started_at']} → {item['finished_at']}, exit0 ; {item['declarations_passed']} déclarations.",
                  f"  Source {item['source_sha256']} ; log {item['log_sha256']} ; olean {item['olean_sha256']}."])
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH22", "time_utc": now,
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch22_attempt01",
              "actual_child_invocations": 2, "modules_passed": 2, "module_count_passed": 2,
              "declarations_passed": 28, "theorems_passed": 22, "definitions_passed": 6,
              "all_current_bytes_preserved": True, "input_count": 8441, "closed_judge_file_count": 1330,
              "protected_archive_count": 3089, "capture_count": 95, "axiom_counts": counts,
              "axiom_rows": all_axioms, "module_evidence": module_evidence,
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"),
              "FIN_sha256": sha(A / "FIN.json"), "gate_sha256": sha(G),
              "metadata_helper_sha256": sha(Path(__file__)), "logs_read_scope": "FULL afad3b",
              "actual_receipt_read_scope": "FULL 711f9d", "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
              "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
              "old_batches_recompiled": False, "author_olean_used": False,
              "official_modules_before_ROOT_observation": 80, "official_declarations_before_ROOT_observation": 1339,
              "hypothetical_after_ROOT_modules": 82, "hypothetical_after_ROOT_declarations": 1367,
              "H1_paid": False, "C5_global_paid": False, "native_refinement_paid": False,
              "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
                  "actual_receipt_sha256": completion["actual_receipt_sha256"],
                  "adjudication_sha256": sha(P / "adjudication.md"),
                  "completion_sha256": sha(P / "completion_receipt.json"), "axiom_counts": counts,
                  "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
