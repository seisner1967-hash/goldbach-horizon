"""Documentary closure of actual26 only: SHA/log JSON, no compiler or candidate import."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch26"
A = P / "batch26_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch26_authorization.json"
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
checked(G, "83ff0267ce700289d0cb24295c4f37e453bedb5e6b69d7fcd3102d6d2c2ec8fe")
assert gate["authorized"] and gate["attempt"] == "batch26_attempt01"
names = ["ComplexGammaMellinLocal22", "ComplexGammaMellinHolomorphy22"]
assert gate["modules"] == names and gate["compiler_invocations_maximum"] == 2
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
checked(A / "receipt.json", "53201e46ee6a6418915358d37a61655a286bd2d814930d0fe68520fec4c92cdb")
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH26_FAILED"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 2
assert receipt["modules_passed"] == 1 and receipt["declarations_passed"] == 22
assert all(receipt[k] is False for k in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 9020
assert len(pre["captures"]) == receipt["capture_count"] == 91
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 1770
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
assert catalog["module_count"] == 2 and catalog["total_declarations"] == 37
assert catalog["theorem_count"] == 27 and catalog["definition_count"] == 10
assert catalog["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == ["GammaPrerequisites22", "ThermalGammaMellinInverse22"]
for dep in catalog["dependency_bindings"]:
    assert dep["status"] == "INDEPENDENT_LEAN_AUX_PASS" and not dep["recompile_authorized"]
    checked(dep["source"], dep["source_sha256"])
    checked(dep["olean_original"], dep["olean_sha256"])
    checked(dep["olean_copy"], dep["olean_sha256"])
    checked(dep["independent_receipt"], dep["independent_receipt_sha256"])

evidence, all_axioms = [], []
for idx, (result, module) in enumerate(zip(receipt["rows"], catalog["modules"], strict=True)):
    name = result["module"]
    assert name == module["module"] == names[idx]
    assert not result["timed_out"] and result["launch_error"] is None
    checked(module["source"], result["source_sha256"])
    checked(module["original_source"], result["source_sha256"])
    checked(A / (name + ".log"), result["log_sha256"])
    log_text = (A / (name + ".log")).read_text(encoding="utf-8-sig")
    assert not re.search(r"\b(?:native_decide|ofReduceBool)\b", log_text)
    pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
    axiom_rows = [{"declaration": n, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]}
                  for n, values in re.findall(pattern, log_text, re.S)]
    assert axiom_rows == result["axiom_rows"]
    assert [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
    assert len(axiom_rows) == len(module["declarations"]) == (22 if idx == 0 else 15)
    assert all(set(row["axioms"]) <= (STANDARD | {"sorryAx"}) for row in axiom_rows)
    counts = {"standard_triplet": sum(set(r["axioms"]) == STANDARD for r in axiom_rows),
              "empty": sum(not r["axioms"] for r in axiom_rows),
              "recovery": sum("sorryAx" in r["axioms"] for r in axiom_rows)}
    errors = re.findall(r"\.lean:(\d+):(\d+): error:([^\n]*)", log_text)
    warnings = re.findall(r"\.lean:(\d+):(\d+): warning:([^\n]*)", log_text)
    if idx == 0:
        assert result["exit_code"] == 0 and result["status"] == "INDEPENDENT_LEAN_AUX_PASS"
        assert result["exact_axiom_coverage_standard_only"] and not errors and not warnings
        assert counts == {"standard_triplet": 22, "empty": 0, "recovery": 0}
        checked(A / (name + ".olean"), result["olean_sha256"])
    else:
        assert result["exit_code"] == 1 and result["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL"
        assert not result["exact_axiom_coverage_standard_only"] and result["olean_sha256"] is None
        assert not (A / (name + ".olean")).exists() and not warnings
        assert counts == {"standard_triplet": 9, "empty": 0, "recovery": 6}
        assert [(int(line), int(col)) for line, col, _ in errors] == [(142,4),(145,68),(157,6),(224,16),(227,18),(232,10),(233,4)]
    mf, ms = read(A / (name + "_FIN.json")), read(A / (name + "_START.json"))
    assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
    assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
    evidence.append({"module": name, "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"],
                     "exit_code": result["exit_code"], "declarations_passed": 22 if idx == 0 else 0,
                     "theorems_passed": 16 if idx == 0 else 0, "definitions_passed": 6 if idx == 0 else 0,
                     "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"],
                     "olean_sha256": result["olean_sha256"], "error_sites": errors, "warning_count": len(warnings),
                     "axiom_counts": counts, "scope": "SCALAR_COMPLEX_GAMMA_MELLIN_AUX_ONLY"})
    all_axioms.extend(axiom_rows)
counts = {"standard_triplet": 31, "empty": 0, "recovery": 6}
lines = ["# Adjudication indépendante — lot26", "",
         "Statut réel INDEPENDENT_BATCH26_FAILED : un module PASS entier, ComplexGammaMellinLocal22, 22 déclarations auxiliaires (16 théorèmes, 6 définitions). ComplexGammaMellinHolomorphy22 échoue, zéro crédit sur ses 15 déclarations. Deux enfants réels, arrêt après cet échec, aucune reprise.", "",
         f"START global {start['time_utc']}, FIN global {fin['time_utc']} ; parent23b2e1/session53965→0bc7a2 exit1. Local START {evidence[0]['started_at']}, FIN {evidence[0]['finished_at']} exit0 ; Holomorphy START {evidence[1]['started_at']}, FIN {evidence[1]['finished_at']} exit1. Aucun timeout ni erreur de lancement.", "",
         "Le vrai PASS Local construit Gamma(2+it) et la puissance complexe principale pour Re(w)>0. Rotation réelle ±η, η=(π/2+|Arg(w)|)/2, décroissance δ=(π/2−|Arg(w)|)/2>0 et coefficient ‖w‖⁻² sec²η ; continuité, intégrabilités sur les deux demi-droites puis volume réel, dérivée ponctuelle en w, accord avec le Mellin réel PASS20. Aucune intégrabilité ou conclusion finale supposée. Les deux dépendances readonly sont exclusivement GammaPrerequisites22 PASS02 et ThermalGammaMellinInverse22 PASS20, jamais recompilées.", "",
         "Sept diagnostics techniques dans Holomorphy :142:4 exp(-(d*t)) face à exp(t*(-d)), normalisation arithmétique manquante ;145:68 addition de fonctions non réduite avant ring ;157:6 composition par la négation non réduite avant simplification ;224:16 et227:18 Tendsto inconnu ;232:10 Eventually.of_forall inconnu (namespace Filter absent) ;233:4 introN en aval des types récupérés. Ces diagnostics ne réfutent ni domination intégrable, ni holomorphie, ni identité analytique sur papier, et n'établissent aucune obstruction de parité. La réparation éventuelle doit être une nouvelle SOURCE sous sélection ROOT.", "",
         "Couverture exacte :22/22 impressions Local, toutes [propext, Classical.choice, Quot.sound], aucune liste vide, récupération ou axiome personnalisé. Holomorphy :15/15 impressions, neuf standards et six sorryAx de récupération, toutes exclues du crédit de module. Ces six sont weightedExponential_integrable, localDerivativeEnvelope_integrable, complexGammaInverse_hasDerivAt, complexGammaInverse_analytic, complexGammaInverse_eq_exp, complex_exp_eq_Gamma_integral. Aucun native_decide/ofReduceBool ni avertissement ;37 noms exacts,31 standards au total ne valent que le crédit entier Local22.", "",
         "Conservation physique après FIN :9020 inputs,1770 anciens Juge (dont lot21 ROLE4 clos),3089 archives,91 captures original/copie et deux dépendances readonly rehashés intacts. Gate/PRE/POST concordent ; Lean4.15/mathlib9837ca9d existants. Aucun olean auteur, ancien compile, numérique ou exécutable natif invoqué.", "",
         "Baseline83 modules/1397 déclarations avant observation ROOT ; seul ajout possible1/22, soit84/1419 après cette observation. Pas de pleine inversion complexe compilée, H1/Weil/traceζΛ, uniformité en phase, correction PP, coefficientN=10^8, D_N ou WIN. Aucun lot27 préparé ici.", "",
         f"Reçu réel {A / 'receipt.json'} SHA {sha(A / 'receipt.json')}.",
         f"PRE {sha(A / 'PREEXEC.json')} ; POST {sha(A / 'POSTEXEC.json')}.",
         f"Local source {evidence[0]['source_sha256']} ; log {evidence[0]['log_sha256']} ; olean {evidence[0]['olean_sha256']}.",
         f"Holomorphy source {evidence[1]['source_sha256']} ; log {evidence[1]['log_sha256']} ; aucune olean.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH26", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch26_attempt01",
              "actual_child_invocations": 2, "modules_passed": 1, "module_count_passed": 1,
              "declarations_passed": 22, "theorems_passed": 16, "definitions_passed": 6,
              "all_current_bytes_preserved": True, "input_count": 9020, "closed_judge_file_count": 1770,
              "protected_archive_count": 3089, "capture_count": 91, "axiom_counts": counts,
              "axiom_rows": all_axioms, "module_evidence": evidence,
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"),
              "FIN_sha256": sha(A / "FIN.json"), "gate_sha256": sha(G),
              "metadata_helper_sha256": sha(Path(__file__)), "logs_read_scope": "FULL221616/dde53a",
              "actual_receipt_read_scope": "FULL7bbe1a", "module_START_FIN_read_scope": "FULL9e243e/221616 plus all JSON rows and moduleFIN exact equality",
              "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
              "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
              "old_batches_recompiled": False, "author_olean_used": False,
              "official_modules_before_ROOT_observation": 83, "official_declarations_before_ROOT_observation": 1397,
              "hypothetical_after_ROOT_modules": 84, "hypothetical_after_ROOT_declarations": 1419,
              "H1_paid": False, "C5_global_paid": False, "complex_Gamma_full_inverse_paid": False,
              "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
                  "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 1, "declarations_passed": 22,
                  "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"),
                  "axiom_counts": counts, "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
