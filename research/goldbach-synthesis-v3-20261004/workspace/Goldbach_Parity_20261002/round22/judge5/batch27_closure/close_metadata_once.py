"""Documentary closure of actual27 only: JSON/current SHA, no candidate or compiler."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch27"
A = P / "batch27_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch27_authorization.json"
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
checked(G, "9d043f99858791e0bc0395e77138f43b09f50e7617516d49e0f57352bd0c206d")
checked(A / "receipt.json", "63bc0f7463b2c5e42841b30846cda0a44f17bd40c3256e2952248c5e64a86f11")
assert gate["authorized"] and gate["attempt"] == "batch27_attempt01"
names = ["ComplexGammaMellinHolomorphy22"]
assert gate["modules"] == names and gate["compiler_invocations_maximum"] == 1
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH27_AUX_PASS"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == 1 and receipt["declarations_passed"] == 15
assert all(receipt[k] is False for k in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 9138
assert len(pre["captures"]) == receipt["capture_count"] == 94
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 1890
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
assert catalog["module_count"] == 1 and catalog["total_declarations"] == 15
assert catalog["theorem_count"] == 11 and catalog["definition_count"] == 4
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
assert result["exit_code"] == 0 and result["status"] == "INDEPENDENT_LEAN_AUX_PASS"
assert result["exact_axiom_coverage_standard_only"]
checked(module["source"], result["source_sha256"])
checked(module["original_source"], result["source_sha256"])
checked(A / (names[0] + ".log"), result["log_sha256"])
checked(A / (names[0] + ".olean"), result["olean_sha256"])
log_text = (A / (names[0] + ".log")).read_text(encoding="utf-8-sig")
assert not re.search(r"\b(?:sorryAx|native_decide|ofReduceBool)\b", log_text)
assert not re.search(r"\.lean:\d+:\d+: (?:error|warning):", log_text)
pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
axiom_rows = [{"declaration": n, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]}
              for n, values in re.findall(pattern, log_text, re.S)]
assert axiom_rows == result["axiom_rows"]
assert [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == 15
assert all(set(row["axioms"]) == STANDARD for row in axiom_rows)
counts = {"standard_triplet": 15, "empty": 0, "recovery": 0}
mf, ms = read(A / (names[0] + "_FIN.json")), read(A / (names[0] + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = [{"module": names[0], "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"],
             "exit_code": 0, "declarations_passed": 15, "theorems_passed": 11, "definitions_passed": 4,
             "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": result["olean_sha256"],
             "error_sites": [], "warning_count": 0, "axiom_counts": counts, "scope": "SCALAR_COMPLEX_GAMMA_MELLIN_AUX_ONLY"}]
lines = ["# Adjudication indépendante — lot27", "",
         "Statut réel INDEPENDENT_BATCH27_AUX_PASS : ComplexGammaMellinHolomorphy22, 15 déclarations auxiliaires (11 théorèmes, 4 définitions). Un enfant réel, une seule invocation, aucune reprise.", "",
         f"START global {start['time_utc']}, FIN global {fin['time_utc']} ; parent4e8965/session1949→9a21d2 exit0. Module START {result['started_at']}, FIN {result['finished_at']} exit0. Aucun timeout, diagnostic ou avertissement.", "",
         "Pour Re(w)>0, les preuves construisent une boule locale restant dans le demi-plan droit, un majorant intégrable du noyau Gamma(2+it) w^(-(2+it)) et de sa dérivée, puis la dérivation paramétrique par domination et l'holomorphie. La branche est la puissance complexe principale. La décroissance locale δ=(π/2−|Arg(w)|)/4 est strictement positive ; les moments de Laplace et la négation préservant la mesure construisent L1 sur volume réel. Aucune intégrabilité ni identité finale n'est une prémisse gratuite.", "",
         "Le principe d'identité utilise l'accord réel déjà payé PASS20 sur des points réels distincts convergeant vers1. La conclusion exacte payée est exp(-w)=(1/(2π))∫_{t∈ℝ} Gamma(2+it) w^(-(2+it)) dt, pour Re(w)>0, ainsi que sa représentation holomorphe. Les constantes locales ne fournissent pas une enveloppe uniforme jusqu'à Arg(w)=±π/2.", "",
         "Les seules dépendances locales sont GammaPrerequisites22 PASS02, ThermalGammaMellinInverse22 PASS20, ComplexGammaMellinLocal22 vrai rowPASS22 du lot26. Le statut global FAILED26 demeure intact ; son crédit Local est justifié par le rowPASS, sa couverture exacte et l'observation ROOT partial9b7697. Aucune de ces dépendances n'a été recompilée ; aucun olean auteur n'a été utilisé.", "",
         "Couverture15/15 exacte, tous [propext, Classical.choice, Quot.sound], zéro déclaration sans axiomes, zéro sorryAx, axiome personnalisé, native_decide ou ofReduceBool. Les erreurs techniques archivées26 sont closes ; elles n'avaient pas réfuté la formule analytique.", "",
         "Conservation physique après FIN :9138 inputs,1890 anciens Juge,3089 archives et94 captures original/copie rehashés intacts. PRE/POST et gate concordent. Lean4.15/mathlib9837ca9d existants, aucune installation, ancien lot, banque numérique ou exécutable natif invoqué.", "",
         "Baseline84 modules/1419 déclarations avant observation ROOT ; ajout possible1/15, soit85/1434 après observation physique ROOT seulement. Ce PASS porte sur l'inversion scalaire de Gamma dans Re(w)>0. Les facteurs ζ, échanges infinis Λ, Weil/compte de zéros, C5 global, enveloppes uniformes en phase, coefficientN=10^8, correction PP, D_N et WIN restent ouverts. Aucun lot28 préparé.", "",
         f"Reçu réel {A / 'receipt.json'} SHA {sha(A / 'receipt.json')}.",
         f"PRE {sha(A / 'PREEXEC.json')} ; POST {sha(A / 'POSTEXEC.json')}.",
         f"Source {result['source_sha256']} ; log {result['log_sha256']} ; olean {result['olean_sha256']}.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH27", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch27_attempt01",
              "actual_child_invocations": 1, "modules_passed": 1, "module_count_passed": 1,
              "declarations_passed": 15, "theorems_passed": 11, "definitions_passed": 4,
              "all_current_bytes_preserved": True, "input_count": 9138, "closed_judge_file_count": 1890,
              "protected_archive_count": 3089, "capture_count": 94, "axiom_counts": counts,
              "axiom_rows": axiom_rows, "module_evidence": evidence,
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"),
              "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)),
              "logs_read_scope": "FULL8395d3", "actual_receipt_read_scope": "FULLb652ee",
              "module_START_FIN_read_scope": "FULL8395d3 plus exact equality to receipt row",
              "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
              "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
              "old_batches_recompiled": False, "author_olean_used": False,
              "official_modules_before_ROOT_observation": 84, "official_declarations_before_ROOT_observation": 1419,
              "hypothetical_after_ROOT_modules": 85, "hypothetical_after_ROOT_declarations": 1434,
              "H1_paid": False, "C5_global_paid": False, "complex_Gamma_full_inverse_paid": True,
              "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
                  "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 1, "declarations_passed": 15,
                  "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"),
                  "axiom_counts": counts, "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
