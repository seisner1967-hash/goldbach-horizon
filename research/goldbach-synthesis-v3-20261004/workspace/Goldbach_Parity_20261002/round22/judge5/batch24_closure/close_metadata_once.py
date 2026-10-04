"""Documentary closure of actual24 only; no compiler, candidate import or numerical work."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch24"
A = P / "batch24_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch24_authorization.json"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = ["AngularMellinBorder22"]

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
catalog, manifest, old = (read(P / name) for name in ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json"))
fin, start, gate = read(A / "FIN.json"), read(A / "START.json"), read(G)
assert gate["authorized"] is True and gate["attempt"] == "batch24_attempt01"
assert gate["modules"] == EXPECTED and gate["compiler_invocations_maximum"] == 1
checked(G, "99c797e8152b46476ebe500fb7d42e5a7fea8ca84c56a9c77774546c219d07d9")
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH24_FAILED"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
assert all(receipt[k] is False for k in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 7855
assert len(pre["captures"]) == receipt["capture_count"] == 81
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 1562
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
assert [row["module"] for row in receipt["rows"]] == EXPECTED
assert catalog["module_count"] == 1 and catalog["total_declarations"] == 30
assert catalog["theorem_count"] == 22 and catalog["definition_count"] == 8
result, module = receipt["rows"][0], catalog["modules"][0]
name = result["module"]
assert name == module["module"]
assert result["exit_code"] == 1 and not result["timed_out"] and result["launch_error"] is None
assert result["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL"
assert result["olean_sha256"] is None and not (A / (name + ".olean")).exists()
checked(module["source"], result["source_sha256"])
checked(module["original_source"], result["source_sha256"])
checked(A / (name + ".log"), result["log_sha256"])
log_text = (A / (name + ".log")).read_text(encoding="utf-8-sig")
assert not re.search(r"\b(?:native_decide|ofReduceBool)\b", log_text)
axiom_rows = [{"declaration": n, "axioms": [v.strip() for v in values.split(",") if v.strip()]}
              for n, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log_text, re.S)]
assert axiom_rows == result["axiom_rows"]
assert [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == 30
assert not re.search(r"does not depend on any axioms", log_text)
assert all(set(row["axioms"]) <= STANDARD | {"sorryAx"} for row in axiom_rows)
counts = {"standard_triplet": sum(set(r["axioms"]) == STANDARD for r in axiom_rows),
          "empty": sum(not r["axioms"] for r in axiom_rows),
          "recovery": sum("sorryAx" in r["axioms"] for r in axiom_rows)}
assert counts == {"standard_triplet": 26, "empty": 0, "recovery": 4}
errors = re.findall(r"\.lean:(\d+):(\d+): error:([^\n]*)", log_text)
warnings = re.findall(r"\.lean:(\d+):(\d+): warning:([^\n]*)", log_text)
assert [int(row[0]) for row in errors] == [123] and len(warnings) == 5
mf, ms = read(A / (name + "_FIN.json")), read(A / (name + "_START.json"))
assert mf == result and ms["time_utc"] == result["started_at"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = {"module": name, "started_at": result["started_at"], "finished_at": result["finished_at"],
            "exit_code": 1, "declarations_passed": 0, "printed_declarations": 30,
            "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"],
            "olean_sha256": None, "error_lines": [123], "warning_count": 5,
            "failure_class": "PROOF_NORMALIZATION_API_COERCIONS"}
lines = ["# Adjudication indépendante — lot24", "", "Statut réel : INDEPENDENT_BATCH24_FAILED. Zéro module et zéro déclaration crédités.", "",
         f"Une seule tentative batch24_attempt01, un enfant Lean : START {start['time_utc']}, FIN global {fin['time_utc']} ; module FIN {result['finished_at']}, exit1, aucun timeout et aucun olean.", "",
         "La source exacte AngularMellinBorder22 révision03 (30 déclarations : 22 théorèmes, 8 définitions) n'a pas compilé. Un diagnostic technique est observé :", "",
         "- Ligne123 : `rw [← inv_pow]` cherche `(a^n)⁻¹`, tandis que le but après les réécritures précédentes est déjà `(-1)⁻¹^N=(-1)^N`. La normalisation inverse-power ajoutée est redondante dans cet état réel.", "",
         "Les diagnostics précédents du dérivé et de la lambda de congrArg ne figurent plus dans ce log. Cela ne donne aucun crédit partiel à ce module entier échoué.", "",
         "Ces diagnostics concernent les raccords de preuve. Ils ne montrent ni contradiction de l'identité analytique sur papier, ni obstruction de parité. La revue SOURCE antérieure reste une revue non élaborée ; elle n'avait attribué aucun PASS.", "",
         "Couverture textuelle exacte : 30 noms/30 prints dans l'ordre du catalogue, 26 listes standard [propext, Classical.choice, Quot.sound], 4 listes avec sorryAx de récupération, aucune liste vide, aucun autre axiome ni native_decide/ofReduceBool. Les quatre déclarations affectées sont angularCharacter_pi, angularIntegral_derivative_eq, angularJ_balance et angularJ_recurrence. Les cinq warnings sont des lint unnecessarySeqFocus. Aucun de ces prints ne donne un crédit partiel à un module ayant échoué.", "",
         "Conservation physique après FIN : 7855 entrées, 1562 anciens fichiers Juge (y compris lot21 ROLE4 clos), 3089 archives et 81 captures source/copie rehashés intacts ; gate et PRE/POST concordent. Zéro dépendance locale, aucun olean auteur, aucune ancienne compilation, aucun banc numérique ou exécutable natif invoqué.", "",
         "La baseline officielle demeure 82 modules/1367 déclarations. H1, C5 global, corrélation globale, coefficient N=10^8, D_N et WIN restent ouverts. Une correction éventuelle doit être une nouvelle source et une nouvelle gate ; cet essai est clos sans reprise.", "",
         f"Reçu réel : {A / 'receipt.json'} ; SHA256 {sha(A / 'receipt.json')}.",
         f"PREEXEC : {sha(A / 'PREEXEC.json')} ; POSTEXEC : {sha(A / 'POSTEXEC.json')}.",
         f"Source {evidence['source_sha256']} ; log {evidence['log_sha256']} ; aucun olean.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH24", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch24_attempt01",
              "actual_child_invocations": 1, "modules_passed": 0, "module_count_passed": 0,
              "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
              "all_current_bytes_preserved": True, "input_count": 7855, "closed_judge_file_count": 1562,
              "protected_archive_count": 3089, "capture_count": 81, "axiom_counts": counts,
              "axiom_rows": axiom_rows, "module_evidence": [evidence],
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"),
              "FIN_sha256": sha(A / "FIN.json"), "gate_sha256": sha(G),
              "metadata_helper_sha256": sha(Path(__file__)), "logs_read_scope": "FULL 4623b2",
              "actual_receipt_read_scope": "FULL 50889c", "module_START_FIN_read_scope": "FULL 50889c START/globalFIN and ffa815 moduleFIN",
              "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
              "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
              "old_batches_recompiled": False, "author_olean_used": False,
              "official_modules_before_ROOT_observation": 82, "official_declarations_before_ROOT_observation": 1367,
              "hypothetical_after_ROOT_modules": 82, "hypothetical_after_ROOT_declarations": 1367,
              "H1_paid": False, "C5_global_paid": False, "native_refinement_paid": False,
              "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
                  "actual_receipt_sha256": completion["actual_receipt_sha256"],
                  "adjudication_sha256": sha(P / "adjudication.md"),
                  "completion_sha256": sha(P / "completion_receipt.json"), "axiom_counts": counts,
                  "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
