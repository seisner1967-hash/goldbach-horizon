"""Documentary closure of actual29: JSON and current SHA only, no compiler/candidate."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch29"
A = P / "batch29_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch29_authorization.json"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()

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
checked(G, "0fa4d88206f02a43e7f580f1552ff9c95553f7908309c1659b4d6fc4f650f9d1")
checked(A / "receipt.json", "15dedac77bad915d04ec44613a4583744db683f430dae0efdf9752377d38e8df")
assert gate["authorized"] and gate["attempt"] == "batch29_attempt01"
names = ["ComplexGammaMellinTail22"]
assert gate["modules"] == names and gate["compiler_invocations_maximum"] == 1
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH29_FAILED"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
assert all(receipt[k] is False for k in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 9389
assert len(pre["captures"]) == receipt["capture_count"] == 100
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 2134
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
assert catalog["module_count"] == 1 and catalog["total_declarations"] == 22
assert catalog["theorem_count"] == 18 and catalog["definition_count"] == 4
assert catalog["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == ["GammaPrerequisites22", "ThermalGammaMellinInverse22", "ComplexGammaMellinLocal22"]
for dep in catalog["dependency_bindings"]:
    assert dep["status"] == "INDEPENDENT_LEAN_AUX_PASS" and not dep["recompile_authorized"]
    assert dep["module_row_and_exact_axioms_verified"]
    checked(dep["source"], dep["source_sha256"])
    checked(dep["olean_original"], dep["olean_sha256"])
    checked(dep["olean_copy"], dep["olean_sha256"])
    checked(dep["independent_receipt"], dep["independent_receipt_sha256"])
    dep_receipt = read(dep["independent_receipt"])
    assert dep_receipt["status"] == dep["independent_receipt_global_status"]
    assert dep_receipt["all_inputs_unchanged"]
    dep_row = next(row for row in dep_receipt["rows"] if row["module"] == dep["module"])
    assert dep_row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and dep_row["exit_code"] == 0
    assert dep_row["source_sha256"] == dep["source_sha256"] and dep_row["olean_sha256"] == dep["olean_sha256"]
    assert dep_row["exact_axiom_coverage_standard_only"]
    if dep["module"] == "ComplexGammaMellinLocal22":
        assert dep_receipt["status"] == "INDEPENDENT_BATCH26_FAILED"
        assert dep["ROOT_partial_observation_required_and_verified"] and len(dep_row["axiom_rows"]) == 22
        checked(B / "round22/judge5/batch26/completion_receipt.json", "6681b27ff6b8be03f471e59e753d7461aa52d6a205bfb872b27b52d77b85678a")
        checked(B / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch26_closed_observation.json", "9b7697d2d35d12903e436403e77fb44e8ea76c6f586940e28d168ab851340e9b")

result, module = receipt["rows"][0], catalog["modules"][0]
assert len(receipt["rows"]) == 1 and result["module"] == module["module"] == names[0]
assert not result["timed_out"] and result["launch_error"] is None
assert result["exit_code"] == 1 and result["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL"
assert not result["exact_axiom_coverage_standard_only"]
assert result["olean_sha256"] is None and not (A / (names[0] + ".olean")).exists()
checked(module["source"], result["source_sha256"])
checked(module["original_source"], result["source_sha256"])
checked(A / (names[0] + ".log"), result["log_sha256"])
log_text = (A / (names[0] + ".log")).read_text(encoding="utf-8-sig")
assert not re.search(r"\b(?:native_decide|ofReduceBool)\b", log_text)
pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
axiom_rows = [{"declaration": n, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]}
              for n, values in re.findall(pattern, log_text, re.S)]
assert axiom_rows == result["axiom_rows"]
assert [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == 22
assert all(set(row["axioms"]) <= STANDARD | {"sorryAx"} for row in axiom_rows)
counts = {"standard_triplet": sum(set(row["axioms"]) == STANDARD for row in axiom_rows),
          "empty": sum(not row["axioms"] for row in axiom_rows),
          "recovery": sum("sorryAx" in row["axioms"] for row in axiom_rows)}
assert counts == {"standard_triplet": 21, "empty": 0, "recovery": 1}
errors = [{"line": int(line), "column": int(column), "message": message}
          for line, column, message in re.findall(r"\.lean:(\d+):(\d+): error: ([^\n]*)", log_text)]
warning_count = len(re.findall(r"\.lean:\d+:\d+: warning:", log_text))
assert len(errors) == 2 and warning_count == 1
mf, ms = read(A / (names[0] + "_FIN.json")), read(A / (names[0] + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = [{"module": names[0], "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"],
             "exit_code": 1, "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
             "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": None,
             "error_sites": errors, "warning_count": warning_count, "axiom_counts": counts,
             "scope": "SCALAR_COMPLEX_GAMMA_MELLIN_TAIL_AUX_ONLY"}]
lines = ["# Adjudication indépendante — lot29", "",
         "Statut réel INDEPENDENT_BATCH29_FAILED : un enfant Tail22, exit1, aucune reprise, aucun olean et zéro crédit. Catalogue exact22 déclarations (18 théorèmes,4 définitions), 22 impressions. Les21 impressions standard ne valident pas le module incomplet.", "",
         f"START global {start['time_utc']}, FIN global {fin['time_utc']} ; parent d66652/session27948→d3a1cd exit1. Module START {result['started_at']}, FIN {result['finished_at']} exit1. Aucun timeout ni erreur de lancement.", "",
         "Deux diagnostics subsistent dans la continuité locale : ligne216:74, ContinuousAt.comp infère g=Prod.mk w au pointH et attend ContinuousAt(Prod.mk w)H, tandis que hp porte sur z↦(z,H) au pointw. Ligne217:4, la composition obtenue reste évaluée enH et ne correspond pas à z↦radius z H évaluée enw. L'annotation de hp n'a donc pas fixé les arguments implicites de comp. Une révision distincte devra fixer explicitement la fonction intérieure et son point, selon la signature réelle. L'avertissement116:58 est une remarque de style indépendante. Les raccords IntegrableOn.mono_set et integral_add_compl corrigés depuis28 ne produisent plus de diagnostics dans ce log. Aucune réfutation analytique ou obstruction de parité n'est déduite de ces erreurs d'inférence.", "",
         "Couverture réelle22/22 :21 triplets [propext,Classical.choice,Quot.sound],0 sans axiomes et1 récupération sorryAx, exactement exists_local_uniform_Gamma_tail. Aucun axiome personnalisé ou mécanisme natif n'est accepté. La récupération interdit tout crédit au module, même aux impressions non contaminées.", "",
         "Portée SOURCE recherchée : vraieGamma(2+it), puissance complexe principale pour Re(w)>0, deux queues signées et rayon R(w,H)=C(w)exp(-δ(w)H)/(πδ(w)), H≥0. La continuité jointe concerne le rayon R; le voisinage final fixeH. La continuité jointe de l'intégrale mobile et une limite localement uniforme H→∞ restent distinctes et ouvertes. Le module ne conclut pas exp(-w), n'importe pas Hol27, et n'offre ni facteurζ, ni échangeΛ, ni signe Goldbach en prémisse.", "",
         "GammaPrerequisites22 PASS02, ThermalGammaMellinInverse22 PASS20 et ComplexGammaMellinLocal22 rowPASS22 du lot26 restent les trois seules dépendances locales readonly. Le reçu26 globalFAILED, le rowPASS et l'observation ROOT partial9b7697 ont été vérifiés. Aucun de ces modules n'a été recompilé, aucun olean auteur n'a été utilisé.", "",
         "Conservation physique après FIN :9389 inputs,2134 anciens Juge,3089 archives et100 captures original/copie rehashés intacts. Toutes les lignes PRE/POST correspondent; gate, sources et dépendances restent inchangées. Lean4.15/mathlib9837ca9d existants; aucune installation, invocation numérique, ancien lot ou exécutable natif.", "",
         "Baseline officielle85 modules/1434 déclarations, zéro ajout par ce lot. Traceζ/Weil, compte de zéros, C5 global, coefficientN=10^8, corrections PP, D_N et WIN restent ouverts. Aucun prochain lot n'est préparé par cette clôture. Une révision SOURCE et sa compilation exigent une nouvelle sélection et une gate ROOT distinctes.", "",
         f"Reçu réel {A / 'receipt.json'} SHA {sha(A / 'receipt.json')}.",
         f"PRE {sha(A / 'PREEXEC.json')} ; POST {sha(A / 'POSTEXEC.json')}.",
         f"Source {result['source_sha256']} ; log {result['log_sha256']} ; aucun olean.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH29", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch29_attempt01",
              "actual_child_invocations": 1, "modules_passed": 0, "module_count_passed": 0,
              "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
              "all_current_bytes_preserved": True, "input_count": 9389, "closed_judge_file_count": 2134,
              "protected_archive_count": 3089, "capture_count": 100, "axiom_counts": counts,
              "axiom_rows": axiom_rows, "module_evidence": evidence,
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"),
              "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)),
              "logs_read_scope": "FULL01d2b2 plus FULLabfab2", "actual_receipt_read_scope": "FULL01d2b2 plus FULLabfab2",
              "module_START_FIN_read_scope": "FULL01d2b2 plus FULLabfab2 plus exact equality to receipt row",
              "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
              "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
              "old_batches_recompiled": False, "author_olean_used": False,
              "official_modules_before_ROOT_observation": 85, "official_declarations_before_ROOT_observation": 1434,
              "hypothetical_after_ROOT_modules": 85, "hypothetical_after_ROOT_declarations": 1434,
              "H1_paid": False, "C5_global_paid": False, "Gamma_tail_integral_paid": False,
              "Gamma_tail_radius_continuity_paid": False, "native_refinement_paid": False,
              "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
                  "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 0, "declarations_passed": 0,
                  "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"),
                  "axiom_counts": counts, "error_count": len(errors), "warning_count": warning_count,
                  "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
