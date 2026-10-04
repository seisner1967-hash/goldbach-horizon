"""Documentary closure of actual25 only: hashes/log JSON; no compiler or candidate import."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch25"
A = P / "batch25_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch25_authorization.json"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
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
catalog, manifest, old = (read(P / name) for name in ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json"))
fin, start, gate = read(A / "FIN.json"), read(A / "START.json"), read(G)
checked(G, "f984a1352b62dace314c5d06f408bd0a8adb44ad7c1b91e66086769d02974742")
assert gate["authorized"] and gate["attempt"] == "batch25_attempt01"
assert gate["modules"] == ["AngularMellinBorder22"] and gate["compiler_invocations_maximum"] == 1
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH25_AUX_PASS"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == 1 and receipt["declarations_passed"] == 30
assert all(receipt[k] is False for k in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 7965
assert len(pre["captures"]) == receipt["capture_count"] == 81
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 1666
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
assert catalog["module_count"] == 1 and catalog["total_declarations"] == 30
assert catalog["theorem_count"] == 22 and catalog["definition_count"] == 8
assert catalog["readonly_local_dependencies"] == [] and receipt["readonly_local_dependencies"] == []
result, module = receipt["rows"][0], catalog["modules"][0]
name = result["module"]
assert name == module["module"] == "AngularMellinBorder22"
assert result["exit_code"] == 0 and not result["timed_out"] and result["launch_error"] is None
assert result["status"] == "INDEPENDENT_LEAN_AUX_PASS" and result["exact_axiom_coverage_standard_only"]
checked(module["source"], result["source_sha256"])
checked(module["original_source"], result["source_sha256"])
checked(A / (name + ".olean"), result["olean_sha256"])
checked(A / (name + ".log"), result["log_sha256"])
log_text = (A / (name + ".log")).read_text(encoding="utf-8-sig")
assert not re.search(r"\b(?:sorryAx|native_decide|ofReduceBool)\b", log_text)
pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
axiom_rows = [{"declaration": n, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]}
              for n, values in re.findall(pattern, log_text, re.S)]
assert axiom_rows == result["axiom_rows"]
assert [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == 30
assert all(set(row["axioms"]) <= STANDARD for row in axiom_rows)
counts = {"standard_triplet": sum(set(r["axioms"]) == STANDARD for r in axiom_rows),
          "empty": sum(not r["axioms"] for r in axiom_rows),
          "recovery": sum("sorryAx" in r["axioms"] for r in axiom_rows)}
assert counts == {"standard_triplet": 30, "empty": 0, "recovery": 0}
assert not re.findall(r"\.lean:(\d+):(\d+): error:", log_text)
warnings = re.findall(r"\.lean:(\d+):(\d+): warning:([^\n]*)", log_text)
assert len(warnings) == 5 and all("Used `tac1 <;> tac2`" in row[2] for row in warnings)
mf, ms = read(A / (name + "_FIN.json")), read(A / (name + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = {"module": name, "started_at": result["started_at"], "finished_at": result["finished_at"],
            "exit_code": 0, "declarations_passed": 30, "theorems_passed": 22, "definitions_passed": 8,
            "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"],
            "olean_sha256": result["olean_sha256"], "error_lines": [], "warning_count": 5,
            "scope": "FINITE_ANGULAR_MELLIN_FTC_BORDER_AUX_ONLY"}
lines = ["# Adjudication indépendante — lot25", "", "Statut réel : INDEPENDENT_BATCH25_AUX_PASS. Un module et 30 déclarations auxiliaires validés (22 théorèmes, 8 définitions).", "",
         f"Une seule tentative batch25_attempt01, un enfant Lean : START global {start['time_utc']}, module START {result['started_at']}, module FIN {result['finished_at']}, FIN global {fin['time_utc']}. Exit0, aucun timeout ; olean indépendante produite.", "",
         "AngularMellinBorder22 révision04 construit la dérivée de la puissance complexe principale et du caractère pour a>0, q complexe quelconque, puis les continuités, les intégrabilités volume sur [-pi,pi] et FTC aux deux bords. Pour N>0 : J(a,N,q)=B(a,N,q)+(q/N)J(a,N,q+1). Le bord B=i(-1)^N[(a-i pi)^(-q)-(a+i pi)^(-q)]/(2 pi N) est conservé : nul à q=0, égal à -(-1)^N/[N(a²+pi²)] et non nul à q=1. Aucune périodicité du cpow, aucun majorant final ou intégrabilité libre ne sont postulés.", "",
         "La seule correction depuis le FAIL24 supprime la réécriture inverse-puissance redondante ; l'ancien lot24 reste clos sans reprise. Cette compilation donne le premier crédit entier de ce module. Les 26 impressions partielles antérieures n'avaient conféré aucun crédit.", "",
         "Couverture exacte : 30 noms / 30 impressions dans l'ordre du catalogue. Chaque déclaration dépend exactement des axiomes standards propext, Classical.choice, Quot.sound. Aucune liste vide, aucune récupération sorryAx, aucun axiome personnalisé, native_decide ou ofReduceBool. Zéro erreur ; cinq avertissements linter unnecessarySeqFocus, sans nouveau run pour les supprimer.", "",
         "Conservation physique après FIN : 7965 entrées, 1666 anciens fichiers Juge (y compris le lot21 ROLE4 clos), 3089 archives et 81 captures original/copie rehashés intacts. Gate/PRE/POST concordent. Zéro dépendance locale ; cache pinned Lean4.15/mathlib9837ca9d, aucun olean auteur, aucune ancienne compilation, aucune invocation numérique ou d'exécutable natif.", "",
         "Baseline officielle 82/1367 avant observation ROOT ; l'ajout possible est exactement 1/30, soit 83/1397 après cette observation seulement. Ce PASS auxiliaire ne paie pas H1, C5 global, trace/corrélation globale, uniformité en phase, correction des puissances premières, coefficient N=10^8, D_N ou WIN. Aucun prochain lot n'est préparé ici.", "",
         f"Reçu réel : {A / 'receipt.json'} ; SHA256 {sha(A / 'receipt.json')}.",
         f"PREEXEC {sha(A / 'PREEXEC.json')} ; POSTEXEC {sha(A / 'POSTEXEC.json')}.",
         f"Source {result['source_sha256']} ; log {result['log_sha256']} ; olean {result['olean_sha256']}.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH25", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch25_attempt01",
              "actual_child_invocations": 1, "modules_passed": 1, "module_count_passed": 1,
              "declarations_passed": 30, "theorems_passed": 22, "definitions_passed": 8,
              "all_current_bytes_preserved": True, "input_count": 7965, "closed_judge_file_count": 1666,
              "protected_archive_count": 3089, "capture_count": 81, "axiom_counts": counts,
              "axiom_rows": axiom_rows, "module_evidence": [evidence],
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"),
              "FIN_sha256": sha(A / "FIN.json"), "gate_sha256": sha(G),
              "metadata_helper_sha256": sha(Path(__file__)), "logs_read_scope": "FULL b56fb0",
              "actual_receipt_read_scope": "FULL 50f15c", "module_START_FIN_read_scope": "FULL f0c6b3/af6e9e",
              "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
              "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
              "old_batches_recompiled": False, "author_olean_used": False,
              "official_modules_before_ROOT_observation": 82, "official_declarations_before_ROOT_observation": 1367,
              "hypothetical_after_ROOT_modules": 83, "hypothetical_after_ROOT_declarations": 1397,
              "H1_paid": False, "C5_global_paid": False, "native_refinement_paid": False,
              "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
                  "actual_receipt_sha256": completion["actual_receipt_sha256"],
                  "adjudication_sha256": sha(P / "adjudication.md"),
                  "completion_sha256": sha(P / "completion_receipt.json"), "axiom_counts": counts,
                  "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
