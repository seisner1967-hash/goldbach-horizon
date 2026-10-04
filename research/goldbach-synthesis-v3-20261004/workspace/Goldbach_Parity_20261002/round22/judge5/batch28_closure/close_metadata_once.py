"""Documentary closure of actual28: JSON and current SHA only, no compiler/candidate."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch28"
A = P / "batch28_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch28_authorization.json"
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
checked(G, "d6dea665b5e99f67d01929bbb4551541e01acaf567ec9a1768d67c7c735e66fa")
checked(A / "receipt.json", "3d724ee2096e676738e55c33c65a36909418930b4a0e40c0a0d7086ad38c06da")
assert gate["authorized"] and gate["attempt"] == "batch28_attempt01"
names = ["ComplexGammaMellinTail22"]
assert gate["modules"] == names and gate["compiler_invocations_maximum"] == 1
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH28_FAILED"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
assert all(receipt[k] is False for k in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 9260
assert len(pre["captures"]) == receipt["capture_count"] == 96
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 2010
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
assert counts == {"standard_triplet": 15, "empty": 0, "recovery": 7}
errors = [{"line": int(line), "column": int(column), "message": message}
          for line, column, message in re.findall(r"\.lean:(\d+):(\d+): error: ([^\n]*)", log_text)]
warning_count = len(re.findall(r"\.lean:\d+:\d+: warning:", log_text))
assert len(errors) == 9 and warning_count == 1
mf, ms = read(A / (names[0] + "_FIN.json")), read(A / (names[0] + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = [{"module": names[0], "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"],
             "exit_code": 1, "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
             "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": None,
             "error_sites": errors, "warning_count": warning_count, "axiom_counts": counts,
             "scope": "SCALAR_COMPLEX_GAMMA_MELLIN_TAIL_AUX_ONLY"}]
lines = ["# Adjudication indépendante — lot28", "",
         "Statut réel INDEPENDENT_BATCH28_FAILED : un enfant Tail22, exit1, aucune reprise et aucun olean. Zéro module et zéro déclaration crédités, malgré 15 impressions standard. Le catalogue contient22 déclarations (18 théorèmes,4 définitions).", "",
         f"START global {start['time_utc']}, FIN global {fin['time_utc']} ; parentec132c/session90361→1eeb16 exit1. Module START {result['started_at']}, FIN {result['finished_at']} exit1. Aucun timeout ni erreur de lancement.", "",
         "Le log contient neuf diagnostics répartis sur trois raccords techniques. Ligne48 : champ Integrable.mono_set inexistant (le second diagnostic And.mono_set vient du dépliage de Integrable). Lignes154–155 : integral_add_compl measurableSet_Icc hi ne fixe pas l'ensemble Icc(-H)H, donc les implicites s/a/b puis le type de have restent inconnus ; le but non résolu126 est une conséquence. Lignes212–213 : la composition de continuité est inférée avec Prod.mk w au pointH, au lieu de z↦(z,H) au pointw. Un avertissement de style115 ne détermine pas l'échec. Ces erreurs ne réfutent pas les bornes analytiques et ne constituent pas une obstruction de parité.", "",
         "Les22 noms imprimés correspondent exactement au catalogue :15 triplets [propext, Classical.choice, Quot.sound],7 contaminés par sorryAx de récupération,0 sans axiomes. Les récupérations concernent exponential_Ioi_integrable, signedGammaTail_integrable, signedGammaTail_norm_le, complexGammaTail_norm_le, complexGammaInverse_sub_truncated_eq_tail, complexGammaInverse_truncation_error_le et exists_local_uniform_Gamma_tail. Aucune impression partielle ne vaut validation du module ; aucun axiome personnalisé ou mécanisme natif n'est accepté.", "",
         "Portée SOURCE déjà revue, encore non certifiée par ce lot : vraieGamma(2+it) et puissance complexe principale sur Re(w)>0, deux queues signées et majorant R(w,H)=C(w)exp(-δ(w)H)/(πδ(w)), H≥0. La continuité jointe recherchée concerne le rayon R, et le voisinage final fixeH ; la continuité jointe de l'intégrale mobile et une limite localement uniforme H→∞ restent distinctes et ouvertes. Aucun théorème d'exp(-w), facteurζ, échangeΛ ou signe Goldbach n'est importé gratuitement.", "",
         "GammaPrerequisites22 PASS02, ThermalGammaMellinInverse22 PASS20 et ComplexGammaMellinLocal22 vrai rowPASS22 du lot26 restent les trois seules dépendances locales readonly. Le globalFAILED26 et son observation ROOT partial9b7697 restent conservés. Aucune dépendance n'a été recompilée et aucun olean auteur utilisé.", "",
         "Conservation physique après FIN :9260 inputs,2010 anciens Juge,3089 archives et96 captures original/copie rehashés intacts. Toutes les lignes PRE/POST concordent ; gate et sources inchangées. Lean4.15/mathlib9837ca9d existants, aucune installation, numérique, ancien lot ou exécutable natif invoqué.", "",
         "Baseline officielle85 modules/1434 déclarations ; zéro ajout possible par ce lot. H1, traceζ/Weil, compte de zéros, C5 global, coefficientN=10^8, corrections PP, D_N et WIN restent ouverts. Aucun lot29 préparé. Une éventuelle révision SOURCE et sa future compilation nécessitent une sélection et une gate ROOT distinctes.", "",
         f"Reçu réel {A / 'receipt.json'} SHA {sha(A / 'receipt.json')}.",
         f"PRE {sha(A / 'PREEXEC.json')} ; POST {sha(A / 'POSTEXEC.json')}.",
         f"Source {result['source_sha256']} ; log {result['log_sha256']} ; aucun olean.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH28", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch28_attempt01",
              "actual_child_invocations": 1, "modules_passed": 0, "module_count_passed": 0,
              "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
              "all_current_bytes_preserved": True, "input_count": 9260, "closed_judge_file_count": 2010,
              "protected_archive_count": 3089, "capture_count": 96, "axiom_counts": counts,
              "axiom_rows": axiom_rows, "module_evidence": evidence,
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"),
              "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)),
              "logs_read_scope": "FULL4b1ed2", "actual_receipt_read_scope": "FULL4b1ed2",
              "module_START_FIN_read_scope": "FULL4b1ed2 plus exact equality to receipt row",
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
