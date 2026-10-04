"""One documentary closure of real FAILED33; existing JSON/bytes only."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch33"
A = P / "batch33_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch33_authorization.json"
MODULE = "ComplexGammaMellinLambda22"
DEPS = ["GammaPrerequisites22", "ThermalGammaMellinInverse22", "ComplexGammaMellinLocal22", "ComplexGammaMellinHolomorphy22"]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PINS = {
    G: "c2f4e13c4b2dbdd103c7f7f2fd40f3aaf100f33abcad24140df48263a350b1d0",
    A / "receipt.json": "5fa2895cce5867ae417f3bec34f1858176c1c10c3b3770005acfa4ae3e2026ef",
    A / "PREEXEC.json": "44e2da0bffc3049978994a740df15fbc447ad50bd2c1db5768b7f783341329f1",
    A / "POSTEXEC.json": "44b4898ea37d0a37fca179f1d668060196c95e4526252c272282bf4830e51ff1",
    A / (MODULE + ".log"): "9193c890ddf67dee7b41ba985ce996582b7d6dc0ac4c3d8d6b55c73fed763bbd",
    P / "catalog.json": "b31f230dc5df62e347c4ee5ea95b09169fd8edddfac4d168908ae79e8720d5c5",
}


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def checked(path, expected, size=None):
    assert sha(path) == expected, str(path)
    if size is not None:
        assert Path(path).stat().st_size == size, str(path)


def write_new(path, text):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


assert not (P / "adjudication.md").exists() and not (P / "completion_receipt.json").exists()
for path, digest in PINS.items():
    checked(path, digest)
receipt, pre, post = (read(A / name) for name in ("receipt.json", "PREEXEC.json", "POSTEXEC.json"))
catalog, manifest, old = (read(P / name) for name in ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json"))
start, fin, gate = read(A / "START.json"), read(A / "FIN.json"), read(G)
assert gate["authorized"] and gate["attempt"] == "batch33_attempt01" and gate["modules"] == [MODULE]
assert gate["compiler_invocations_maximum"] == 1 and gate["prior_modules"] == 87 and gate["prior_declarations"] == 1458
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH33_FAILED"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
assert all(receipt[key] is False for key in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == len(manifest["immutable_inputs"]) == receipt["input_count"] == 9945
assert len(pre["captures"]) == receipt["capture_count"] == 108
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 2673
assert {row["path"]: row["sha256"] for row in manifest["immutable_inputs"]} == {row["path"]: row["sha256"] for row in pre["inputs"]}
for row in manifest["immutable_inputs"] + old["inputs"]:
    checked(row["path"], row["sha256"], row["bytes"])
for row in pre["protected_archives"]:
    path = Path(row["path"])
    checked(path if path.is_absolute() else B / path, row["sha256"])
for row in pre["captures"]:
    checked(row["source"], row["sha256"])
    checked(row["capture"], row["sha256"])
assert catalog["module_count"] == 1 and catalog["total_declarations"] == 30
assert catalog["theorem_count"] == 24 and catalog["definition_count"] == 6
assert catalog["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == DEPS
for dep in catalog["dependency_bindings"]:
    assert dep["status"] == "INDEPENDENT_LEAN_AUX_PASS" and not dep["recompile_authorized"]
    assert dep["module_row_and_exact_axioms_verified"]
    for key, digest in (("source", dep["source_sha256"]), ("olean_original", dep["olean_sha256"]), ("olean_copy", dep["olean_sha256"]), ("independent_receipt", dep["independent_receipt_sha256"])):
        checked(dep[key], digest)
    dep_receipt = read(dep["independent_receipt"])
    assert dep_receipt["status"] == dep["independent_receipt_global_status"] and dep_receipt["all_inputs_unchanged"]
    dep_row = next(row for row in dep_receipt["rows"] if row["module"] == dep["module"])
    assert dep_row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and dep_row["exit_code"] == 0
    assert dep_row["source_sha256"] == dep["source_sha256"] and dep_row["olean_sha256"] == dep["olean_sha256"]
    assert dep_row["exact_axiom_coverage_standard_only"]
    if dep["module"] == "ComplexGammaMellinLocal22":
        assert dep_receipt["status"] == "INDEPENDENT_BATCH26_FAILED" and dep["ROOT_partial_observation_required_and_verified"]
    if dep["module"] == "ComplexGammaMellinHolomorphy22":
        assert dep["ROOT_closed_observation_required_and_verified"]
result, module = receipt["rows"][0], catalog["modules"][0]
assert len(receipt["rows"]) == 1 and result["module"] == module["module"] == MODULE
assert result["exit_code"] == 1 and result["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL"
assert not result["timed_out"] and result["launch_error"] is None and not result["exact_axiom_coverage_standard_only"]
assert result["olean_sha256"] is None and not (A / (MODULE + ".olean")).exists()
checked(module["source"], result["source_sha256"])
checked(module["original_source"], result["source_sha256"])
log_text = (A / (MODULE + ".log")).read_text(encoding="utf-8-sig")
pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
axiom_rows = [{"declaration": name, "axioms": [word.strip() for word in (values or "").replace("\n", " ").split(",") if word.strip()]} for name, values in re.findall(pattern, log_text, re.S)]
assert axiom_rows == result["axiom_rows"] and [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == len({row["declaration"] for row in axiom_rows}) == 30
assert all(set(row["axioms"]) <= STANDARD | {"sorryAx"} and len(row["axioms"]) == len(set(row["axioms"])) for row in axiom_rows)
assert not re.search(r"\b(?:native_decide|ofReduceBool)\b", log_text)
counts = {"standard_triplet": sum(set(row["axioms"]) == STANDARD for row in axiom_rows), "empty": sum(not row["axioms"] for row in axiom_rows), "recovery": sum("sorryAx" in row["axioms"] for row in axiom_rows)}
assert counts == {"standard_triplet": 25, "empty": 0, "recovery": 5}
errors = re.findall(r"\.lean:(\d+):(\d+): error: ([^\n]*)", log_text)
warnings = re.findall(r"\.lean:(\d+):(\d+): warning: ([^\n]*)", log_text)
assert errors == [("149", "4", "type mismatch, term")] and warnings == [("181", "62", "unused variable `hw`")]
mf, ms = read(A / (MODULE + "_FIN.json")), read(A / (MODULE + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = [{"module": MODULE, "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"], "exit_code": 1, "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0, "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": None, "error_sites": errors, "warning_count": 1, "axiom_counts": counts, "scope": "TRUE_LAMBDA_COMPLEX_GAMMA_MELLIN_AUX_ONLY"}]
lines = ["# Adjudication indépendante — lot 33", "", "Statut réel INDEPENDENT_BATCH33_FAILED : un enfant, exit1, aucun olean, aucun timeout ni reprise. Zéro module et zéro déclaration crédités. Le catalogue demeure exact :24 théorèmes/6 définitions/30 prints.", "", f"Parent b748aa/session9762→31f18e exit1. TOOL_START2026-10-04T02:32:24.7145794Z, TOOL_FIN2026-10-04T02:33:38.6281999Z. START global {start['time_utc']}, FIN global {fin['time_utc']}; module {result['started_at']}→{result['finished_at']}.", "", "Log réellement lu FULL53146b, receipt FULLa6f02a, START/FIN et hashes FULL98e201. Un diagnostic149:4 : continuous_const simplifié a le type Continuous(fun x=>0), tandis que le but Continuous(lambdaMellinCoefficient0) reste non réduit au cas n=0. C'est un raccord de normalisation de preuve, sans réfutation analytique ni obstruction de parité déduite. Avertissement181:62 : variable hw inutilisée, sans autre erreur. Les deux autres blocs corrigés après31 n'émettent plus de diagnostic; ils ne donnent aucun crédit partiel du module.", "", "Couverture textuelle indépendante :30 noms exacts dans l'ordre du catalogue,25 triplets standards [propext,Classical.choice,Quot.sound],0 liste vide,5 récupérations sorryAx. Les récupérations affectent coefficient_continuous, Dirichlet_continuous, Integrand_integrable, Product_integrable et Thermal_eq_integral. Elles empêchent tout crédit entier. Le journal ne contient aucun mécanisme natif ou axiome personnalisé distinct; aucun nouveau sorry/admit n'a été écrit dans la SOURCE gelée.", "", "La portée SOURCE reste la vraie série vonMangoldt, avec puissances premières, Q≤6, L1 construit et échange infini Γ–Λ sur Re(w)>0. Cette tentative ne certifie pas le module. La revue mathématique SOURCE indépendante694657… et ses lectures ne sont pas un PASS Lean. Gamma02/Thermal20/Local26/Holo27 restent quatre vrais readonly, avec Local26 rowPASS malgré globalFAILED et observation ROOT partielle, sans recompilation ni olean auteur.", "", "Conservation physique après FIN :9945 inputs,2673 anciens fichiers Juge,3089 archives et108 captures source/copie rehashés intacts. PRE/POST concordent, gate/sources/dépendances immuables. Les outils34 créés après PREP33 sont hors de son ancien snapshot. Cette clôture ne fait que JSON/SHA et deux pièces documentaires, zéro compilateur/candidat/numérique.", "", "Baseline87/1458 inchangée, à confirmer par observation ROOT. Ni Γ–Λ final, queue pondérée, ζ/Weil, annulation signée, correction PP/front, coefficientN=10^8, D_N ni WIN ne sont acquis ici.", "", f"Receipt {sha(A / 'receipt.json')}; PRE {sha(A / 'PREEXEC.json')}; POST {sha(A / 'POSTEXEC.json')}; log {result['log_sha256']}.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH33", "time_utc": datetime.now(timezone.utc).isoformat(), "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch33_attempt01", "actual_child_invocations": 1, "modules_passed": 0, "module_count_passed": 0, "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0, "all_current_bytes_preserved": True, "input_count": 9945, "closed_judge_file_count": 2673, "protected_archive_count": 3089, "capture_count": 108, "axiom_counts": counts, "axiom_rows": axiom_rows, "module_evidence": evidence, "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"), "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"), "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"), "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)), "logs_read_scope": "FULL53146b", "actual_receipt_read_scope": "FULLa6f02a", "module_START_FIN_read_scope": "FULL589616 and exact equality to real receipt row", "large_PRE_POST_read_scope": "HEADER_PROJECTION_PLUS_ALL_METADATA_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL", "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0, "old_batches_recompiled": False, "author_olean_used": False, "official_modules_before_ROOT_observation": 87, "official_declarations_before_ROOT_observation": 1458, "hypothetical_after_ROOT_modules": 87, "hypothetical_after_ROOT_declarations": 1458, "H1_paid": False, "C5_global_paid": False, "Lambda_Mellin_paid_by_this_module": False, "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True, "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 0, "declarations_passed": 0, "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"), "axiom_counts": counts, "error_count": 1, "warning_count": 1, "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
