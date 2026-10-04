"""Close the actual failed batch31 once: JSON/SHA/documentary output only."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch31"
A = P / "batch31_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch31_authorization.json"
MODULE = "ComplexGammaMellinLambda22"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def checked(path, expected, expected_bytes=None):
    assert sha(path) == expected, str(path)
    if expected_bytes is not None:
        assert Path(path).stat().st_size == expected_bytes, str(path)


def write_new(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(value)


assert not (P / "adjudication.md").exists()
assert not (P / "completion_receipt.json").exists()
receipt, pre, post = (read(A / name) for name in ("receipt.json", "PREEXEC.json", "POSTEXEC.json"))
catalog, manifest, old = (read(P / name) for name in ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json"))
fin, start, gate = read(A / "FIN.json"), read(A / "START.json"), read(G)
checked(G, "6ae2ba37d3a90b5a19b228257dc37b8e102db939843fa0a79334184fc2d8e571")
checked(A / "receipt.json", "470f798110abde794b6742605c5dc66e4c7aabe7bc6a9e81e502e3c41aab9d1c")
checked(A / "PREEXEC.json", "3507c7ee4b346bb7dd6c67b27b4ed8b98d0ec301860cb65cd15cd0d1bc8d6e26")
checked(A / "POSTEXEC.json", "ef98decc9dac7a0f7798d5cc9afd01187007db7276a3ca8a497e639e8ec79ec8")
assert gate["authorized"] and gate["attempt"] == "batch31_attempt01"
assert gate["modules"] == [MODULE] and gate["compiler_invocations_maximum"] == 1
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
checked(P / "catalog.json", "82851300c705149a130649857bb9c228a20240c53afd9bd80374e91bc2d6a56d")
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH31_FAILED"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
assert all(receipt[key] is False for key in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 9657
assert len(pre["captures"]) == receipt["capture_count"] == 107
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 2397
assert len(manifest["immutable_inputs"]) == len(pre["inputs"])
assert {row["path"]: row["sha256"] for row in manifest["immutable_inputs"]} == {row["path"]: row["sha256"] for row in pre["inputs"]}
for row in manifest["immutable_inputs"]:
    checked(row["path"], row["sha256"], row["bytes"])
for row in old["inputs"]:
    checked(row["path"], row["sha256"], row["bytes"])
for row in pre["protected_archives"]:
    path = Path(row["path"])
    checked(path if path.is_absolute() else B / path, row["sha256"])
for row in pre["captures"]:
    checked(row["source"], row["sha256"])
    checked(row["capture"], row["sha256"])
assert catalog["module_count"] == 1 and catalog["total_declarations"] == 30
assert catalog["theorem_count"] == 24 and catalog["definition_count"] == 6
assert catalog["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == [
    "GammaPrerequisites22", "ThermalGammaMellinInverse22", "ComplexGammaMellinLocal22", "ComplexGammaMellinHolomorphy22"]
for dep in catalog["dependency_bindings"]:
    assert dep["status"] == "INDEPENDENT_LEAN_AUX_PASS" and not dep["recompile_authorized"]
    assert dep["module_row_and_exact_axioms_verified"]
    for path, digest in ((dep["source"], dep["source_sha256"]), (dep["olean_original"], dep["olean_sha256"]),
                         (dep["olean_copy"], dep["olean_sha256"]), (dep["independent_receipt"], dep["independent_receipt_sha256"])):
        checked(path, digest)
    dep_receipt = read(dep["independent_receipt"])
    assert dep_receipt["status"] == dep["independent_receipt_global_status"] and dep_receipt["all_inputs_unchanged"]
    dep_row = next(row for row in dep_receipt["rows"] if row["module"] == dep["module"])
    assert dep_row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and dep_row["exit_code"] == 0
    assert dep_row["source_sha256"] == dep["source_sha256"] and dep_row["olean_sha256"] == dep["olean_sha256"]
    assert dep_row["exact_axiom_coverage_standard_only"]
    if dep["module"] == "ComplexGammaMellinLocal22":
        assert dep_receipt["status"] == "INDEPENDENT_BATCH26_FAILED" and len(dep_row["axiom_rows"]) == 22
        assert dep["ROOT_partial_observation_required_and_verified"]
    if dep["module"] == "ComplexGammaMellinHolomorphy22":
        assert dep_receipt["status"] == "INDEPENDENT_BATCH27_AUX_PASS" and len(dep_row["axiom_rows"]) == 15
        assert dep["ROOT_closed_observation_required_and_verified"]

result, module = receipt["rows"][0], catalog["modules"][0]
assert len(receipt["rows"]) == 1 and result["module"] == module["module"] == MODULE
assert not result["timed_out"] and result["launch_error"] is None
assert result["exit_code"] == 1 and result["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL"
assert not result["exact_axiom_coverage_standard_only"] and result["olean_sha256"] is None
assert not (A / (MODULE + ".olean")).exists()
checked(module["source"], "c0653c546413d5f2aac9715a301303c2ac5750dca5d96054bfb450c91ab3249c")
checked(module["original_source"], result["source_sha256"])
checked(A / (MODULE + ".log"), result["log_sha256"])
log_text = (A / (MODULE + ".log")).read_text(encoding="utf-8-sig")
assert not re.search(r"\b(?:native_decide|ofReduceBool)\b", log_text)
pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
axiom_rows = [{"declaration": name, "axioms": [word.strip() for word in (values or "").replace("\n", " ").split(",") if word.strip()]}
              for name, values in re.findall(pattern, log_text, re.S)]
assert axiom_rows == result["axiom_rows"]
assert [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == 30
assert all(set(row["axioms"]) <= STANDARD | {"sorryAx"} for row in axiom_rows)
counts = {"standard_triplet": sum(set(row["axioms"]) == STANDARD for row in axiom_rows),
          "empty": sum(not row["axioms"] for row in axiom_rows),
          "recovery": sum("sorryAx" in row["axioms"] for row in axiom_rows)}
assert counts == {"standard_triplet": 20, "empty": 0, "recovery": 10}
errors = [{"line": int(line), "column": int(column), "message": message}
          for line, column, message in re.findall(r"\.lean:(\d+):(\d+): error: ([^\n]*)", log_text)]
assert [(item["line"], item["column"]) for item in errors] == [(84, 12), (85, 8), (85, 43), (110, 72), (146, 4)]
warning_count = len(re.findall(r"\.lean:\d+:\d+: warning:", log_text))
assert warning_count == 1
mf, ms = read(A / (MODULE + "_FIN.json")), read(A / (MODULE + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = [{"module": MODULE, "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"],
    "exit_code": 1, "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
    "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": None,
    "error_sites": errors, "warning_count": warning_count, "axiom_counts": counts,
    "scope": "TRUE_LAMBDA_COMPLEX_GAMMA_MELLIN_AUX_ONLY", "failure_class": "API_NOTATION_AND_SIMPLIFICATION"}]
lines = ["# Adjudication indépendante — lot 31", "",
    "Statut réel INDEPENDENT_BATCH31_FAILED. Un seul enfant mainΛ SOURCE01, exit1, sans timeout ni erreur de lancement, aucun olean. Zéro crédit du module entier et zéro déclaration acquise, malgré20 impressions standards. Aucun retry ou ancien module recompilé.", "",
    f"START global {start['time_utc']}, FIN global {fin['time_utc']}. Enfant START {result['started_at']}, FIN {result['finished_at']}. Parent82d1fe/session53567 →e7fcc6 exit1 ; TOOL_START01:32:37.2565882UTC, TOOL_FIN01:33:42.1356176UTC.", "",
    "Journal intégral FULLf8ec56, reçu FULL1a8b93, module START/FIN FULL1884a4, global START004edb/FINc8ee6f. Cinq diagnostics exacts sur trois raccords :84:12 Membership ℝ(List(Listℝ)), la notation [[1,1+K]] étant interprétée comme liste plutôt que uIcc ;85:8 rewrite uIcc absent et85:43 argument de le_add_of_nonneg_right non typé par le but récupéré ;110:72 norm_num laisse la somme Finset.range2 ;146:4 simp made no progress dans la branche n=0 de lambdaMellinCoefficient_continuous. Un avertissement unused hw178:62.", "",
    "Ces diagnostics portent sur notation, coercions et simplification. Ils ne démontrent aucune réfutation analytique de Q≤6, du transport de branche ou de l'échange somme/intégrale, et ne constituent pas une obstruction de parité. Les preuves restent non validées pour ce module. Les sites ont été transmis à ROLE4 ; toute réparation doit être une SOURCE distincte sous nouvelle sélection/gate, jamais une reprise de cette tentative.", "",
    "Catalogue candidat30=24 théorèmes/6 définitions, noms et ordre exacts des30 prints observés. Axiomes réels :20 triplets [propext, Classical.choice, Quot.sound],0 liste vide,10 récupérations sorryAx. Les récupérations sont conservées explicitement et rejetées comme preuve ; aucune promotion partielle des20 autres prints. Aucun axiome personnalisé ou mécanisme natif observé.", "",
    "Portée SOURCE prévue seulement : vraieΛ, toutes puissances de premiers comprises, Q=ΣΛ(n)n^(-2)≤6, noyau principalΓ(2+it)w^(-2-it), domaine Re(w)>0, L1 et échange infini construits. La cible intégrale finale n'est pas offerte en prémisse. Aucune de ces conclusions du candidat n'est acquise par cette tentative FAILED. Les preuves indépendantes Gamma02/Thermal20/Local26/Holo27 antérieures restent acquises readonly ; Local26 conserve global26FAILED et rowPASS22/ROOTpartial.", "",
    "Conservation physique après FIN :9657 inputs,2397 anciens fichiers Juge,3089 archives et107 captures original/copie rehashés intacts. Toutes les lignes PRE/POST correspondent. Gate, sources et quatre oleans readonly originaux/copies inchangés. La clôture exécute seulement JSON/SHA et produit deux documents ; zéro Lean, import candidat, numérique ou exécutable natif.", "",
    "Baseline officielle86 modules/1456 déclarations auxiliaires, inchangée par zéro crédit31. Bridge2, EΛ16, identification−ζ′/ζ, zéros/Weil, annulation signée, PP/front, coefficientN=10⁸, D_N et WIN restent ouverts.", "",
    f"Reçu réel {A / 'receipt.json'} SHA {sha(A / 'receipt.json')}.",
    f"PRE {sha(A / 'PREEXEC.json')} ; POST {sha(A / 'POSTEXEC.json')}.",
    f"Source {result['source_sha256']} ; log {result['log_sha256']} ; olean absent.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH31", "time_utc": datetime.now(timezone.utc).isoformat(),
    "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch31_attempt01",
    "actual_child_invocations": 1, "modules_passed": 0, "module_count_passed": 0,
    "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0,
    "all_current_bytes_preserved": True, "input_count": 9657, "closed_judge_file_count": 2397,
    "protected_archive_count": 3089, "capture_count": 107, "axiom_counts": counts,
    "axiom_rows": axiom_rows, "module_evidence": evidence,
    "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
    "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
    "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"),
    "module_START_sha256": sha(A / (MODULE + "_START.json")), "module_FIN_sha256": sha(A / (MODULE + "_FIN.json")),
    "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)),
    "logs_read_scope": "FULLf8ec56", "actual_receipt_read_scope": "FULL1a8b93",
    "module_START_FIN_read_scope": "FULL1884a4 plus exact equality to receipt row",
    "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
    "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
    "old_batches_recompiled": False, "author_olean_used": False,
    "official_modules_before_ROOT_observation": 86, "official_declarations_before_ROOT_observation": 1456,
    "hypothetical_after_ROOT_modules": 86, "hypothetical_after_ROOT_declarations": 1456,
    "failure_class": "API_NOTATION_AND_SIMPLIFICATION", "mathematical_refutation_observed": False,
    "H1_paid": False, "C5_global_paid": False, "Lambda_Mellin_identity_paid_by_this_module": False,
    "Lambda_weighted_tail_paid": False, "native_refinement_paid": False,
    "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
    "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 0, "declarations_passed": 0,
    "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"),
    "axiom_counts": counts, "error_count": len(errors), "warning_count": warning_count,
    "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
