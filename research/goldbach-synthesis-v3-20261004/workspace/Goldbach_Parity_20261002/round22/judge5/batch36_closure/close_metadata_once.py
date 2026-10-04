"""Close the unique FAILED36: documentary JSON/log/byte-hash audit only."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch36"
A = P / "batch36_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch36_authorization.json"
M = "ComplexGammaMellinLambdaTail22"
NEXT = "ComplexGammaCircleGeometry22"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PINS = {
    G: "a86b4dd45ae154266a91c9a01b6e4a236a4048eba86cc6b77dac181051ab59d9",
    A / "receipt.json": "4307d388d3dac634c08c9e342538bab45bf4c10945898ddc0ae453959c0574e7",
    A / "PREEXEC.json": "c67ce107860a173361edb900aa53e3ee9a08fdc4a7b6379e64d2210b8f5d4d2d",
    A / "POSTEXEC.json": "181b9e1d412b59ee2efd13fbb4f0fe552540223ccf9e2c6f6d2834975ec83f4f",
    A / (M + ".log"): "cf48c948d8ff6de63793d7aa8410802f3c035f31bfcc3f07b8deb601f25d6d6e",
    A / (M + "_FIN.json"): "6ed445296daf7da9ab32f9b44014445af058c6f3a6f53ee5acc3ac16e6dcd8dc",
    P / "catalog.json": "d11bc89b86e0d06ca0d2d083d81c07c7f99d4b8e42326d772558f6831b065904",
}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            h.update(block)
    return h.hexdigest()


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
gate, start, fin = read(G), read(A / "START.json"), read(A / "FIN.json")
assert gate["authorized"] and gate["attempt"] == "batch36_attempt01" and gate["modules"] == [M, NEXT]
assert gate["compiler_invocations_maximum"] == 2 and gate["prior_modules"] == 88 and gate["prior_declarations"] == 1488
assert gate["child_wall_seconds"] == 300 and gate["max_heartbeats"] == 1000000 and gate["retry_count_maximum"] == 0
for name, key in (("prepared_manifest.json", "source_manifest_sha256"), ("run_once.py", "launcher_sha256"), ("prepared_receipt.json", "preparation_receipt_sha256")):
    checked(P / name, gate[key])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH36_FAILED"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == len(receipt["rows"]) == 1
assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
assert all(receipt[key] is False for key in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == len(manifest["immutable_inputs"]) == receipt["input_count"] == 10246
assert len(pre["captures"]) == receipt["capture_count"] == 125
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 2957
assert {r["path"]: r["sha256"] for r in manifest["immutable_inputs"]} == {r["path"]: r["sha256"] for r in pre["inputs"]}
for row in manifest["immutable_inputs"] + old["inputs"]:
    checked(row["path"], row["sha256"], row["bytes"])
for row in pre["protected_archives"]:
    path = Path(row["path"])
    checked(path if path.is_absolute() else B / path, row["sha256"])
for row in pre["captures"]:
    checked(row["source"], row["sha256"])
    checked(row["capture"], row["sha256"])
assert catalog["module_count"] == 2 and catalog["total_declarations"] == 41
assert catalog["theorem_count"] == 34 and catalog["definition_count"] == 7
assert [m["module"] for m in catalog["modules"]] == [M, NEXT]
assert len(catalog["readonly_local_dependencies"]) == 6
assert catalog["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == gate["readonly_local_dependencies"]
for dep in catalog["dependency_bindings"]:
    assert dep["status"] == "INDEPENDENT_LEAN_AUX_PASS" and not dep["recompile_authorized"]
    assert dep["module_row_and_exact_axioms_verified"]
    for key, digest in (("source", dep["source_sha256"]), ("olean_original", dep["olean_sha256"]), ("olean_copy", dep["olean_sha256"]), ("independent_receipt", dep["independent_receipt_sha256"])):
        checked(dep[key], digest)
    dependency_receipt = read(dep["independent_receipt"])
    assert dependency_receipt["status"] == dep["independent_receipt_global_status"] and dependency_receipt["all_inputs_unchanged"]
    dependency_row = next(r for r in dependency_receipt["rows"] if r["module"] == dep["module"])
    assert dependency_row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and dependency_row["exit_code"] == 0
    assert dependency_row["source_sha256"] == dep["source_sha256"] and dependency_row["olean_sha256"] == dep["olean_sha256"]
    assert dependency_row["exact_axiom_coverage_standard_only"]
    if dep["module"] == "ComplexGammaMellinLocal22":
        assert dependency_receipt["status"] == "INDEPENDENT_BATCH26_FAILED" and dep["ROOT_closed_observation_verified"]
result, module = receipt["rows"][0], catalog["modules"][0]
assert result["module"] == M and result["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL" and result["exit_code"] == 1
assert not result["timed_out"] and result["launch_error"] is None and not result["exact_axiom_coverage_standard_only"]
assert result["olean_sha256"] is None and not (A / (M + ".olean")).exists()
for suffix in (".log", ".olean", "_START.json", "_FIN.json"):
    assert not (A / (NEXT + suffix)).exists()
for entry in catalog["modules"]:
    checked(entry["source"], entry["source_sha256"])
    checked(entry["original_source"], entry["source_sha256"])
log = (A / (M + ".log")).read_text(encoding="utf-8-sig")
rows = [{"declaration": n, "axioms": [s.strip() for s in (v or "").replace("\n", " ").split(",") if s.strip()]} for n, v in re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)]
assert rows == result["axiom_rows"] and [r["declaration"] for r in rows] == module["qualified_prints"]
assert len(rows) == len(module["declarations"]) == len({r["declaration"] for r in rows}) == 16
assert all(len(r["axioms"]) == len(set(r["axioms"])) and set(r["axioms"]) <= STANDARD | {"sorryAx"} for r in rows)
recovery = [r["declaration"] for r in rows if "sorryAx" in r["axioms"]]
assert recovery == ["GoldbachComplexGammaMellin22." + n for n in ("signedLambdaMellinTail_true_eq_Iio", "lambdaMellinThermal_sub_truncated_eq_tail", "lambdaMellinThermal_truncation_error_le")]
counts = {"standard_triplet": 13, "empty": 0, "recovery": 3, "custom_or_native": 0}
assert sum(set(r["axioms"]) == STANDARD for r in rows) == 13 and all(r["axioms"] for r in rows)
assert not re.search(r"\b(?:native_decide|ofReduceBool)\b", log)
errors = re.findall(r"\.lean:(\d+):(\d+): error: ([^\n]*)", log)
warnings = re.findall(r"\.lean:(\d+):(\d+): warning: ([^\n]*)", log)
assert len(errors) == 1 and errors[0][:2] == ("118", "6") and "rewrite" in errors[0][2]
assert len(warnings) == 1 and warnings[0][:2] == ("110", "58")
module_fin, module_start = read(A / (M + "_FIN.json")), read(A / (M + "_START.json"))
assert module_fin == result and module_start["command"] == result["command"] and module_start["gate_sha256"] == sha(G)
assert start["time_utc"] <= module_start["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
evidence = [{"module": M, "status": result["status"], "exit_code": 1, "started_at": result["started_at"], "finished_at": result["finished_at"], "declarations_passed": 0, "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": None, "error_sites": errors, "warning_count": 1, "axiom_counts": counts}, {"module": NEXT, "status": "NON_INVOKED_STOP_FIRST_FAILURE", "exit_code": None, "declarations_passed": 0, "source_sha256": catalog["modules"][1]["source_sha256"], "observed_prints": 0}]
lines = ["# Adjudication indépendante — lot36", "", "INDEPENDENT_BATCH36_FAILED : une seule compilation, exit1, aucun olean ; Geometry25 NON_INVOKED_STOP_FIRST_FAILURE. Crédit entier0modules/0déclarations, malgré13 prints standard. Aucune reprise ni réparation dans ce lot.", "", f"Parent529fd3/session93620→a2cbf1 exit1 ; TOOL_START2026-10-04T04:08:34.8956883Z, TOOL_FIN2026-10-04T04:09:31.2165391Z. STARTglobal {start['time_utc']}, FINglobal {fin['time_utc']}; EΛ {result['started_at']}→{result['finished_at']}.", "", "Log/moduleFIN/STARTglobal/FINglobal propres FULL6d0298 ; receipt propre FULLa50f11 ; grande PRE/POST projection91ef5a puis toutes entrées et bytes vérifiés par ce helper. Le contrôle ne revendique aucune rawFULL des sources de tout le cache.", "", "Unique erreur118:6 dans signedLambdaMellinTail_true_eq_Iio : rw ne reconnaît pas ∫IoiH, f(-t) dans le produit D(-t)*K(w,-t). La signature réelle integral_comp_neg_Ioi(c)(f) est lue TARGETEDa50f11 aux lignes86–98 du cache Lebesgue/Integral.lean. Il s'agit d'un raccord d'inférence/forme du lambda produit pour une réflexion exacte, pas d'une réfutation analytique ou d'un diagnostic de parité. Aucun correctif n'est exécuté ici. Seul linter110:58 unnecessarySeqFocus.", "", "Les16 noms EΛ sont imprimés une fois et dans l'ordre du catalogue :13 triplets propext/Classical.choice/Quot.sound,0liste vide,3recovery sorryAx (réflexion, identité de troncature et erreur de troncature). Cette récupération exclut le PASS du module entier. Aucun print Geometry, aucune olean neuve. La portée scientifique et ses domaines restent SOURCE non validés pour ces deux modules.", "", "Les six dépendances indépendantes Γ02/Thermal20/Local26/Holo27/Tail30/main35 restent readonly sans recompilation ni olean auteur. Local26 conserve son globalFAILED et sa seule rowPASS22 observée ; main35 est bien source03 payée. Sources historiques pending/FAILED et sixDRAFT34 STOPPED préservés.", "", "Conservation physique indépendante après FIN :10246inputs/2957anciensJuge/3089archives/125captures source et copie inchangés. PRE/POST/gate/receipts/oleans readonly sont conformes. Clôture exclusivement JSON/logs/SHA et documentation, sans nouveau Lean, probe ou numérique.", "", "Baseline officielle88/1488 inchangée ; aucune hypothèse d'incrément. L'enveloppe Λ, la géométrie, leur assemblage uniforme, coefficientN=10^8, ζ/Weil, PP/front, D_N et WIN ne sont pas acquis par ce lot. Les domaines Rew>0,H≥0 et a>0,|θ|≤π restent ceux des sources, sans prémisse de signe ajoutée.", "", f"ReceiptSHA {sha(A / 'receipt.json')}; PRE {sha(A / 'PREEXEC.json')}; POST {sha(A / 'POSTEXEC.json')}; log {result['log_sha256']}.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH36", "time_utc": datetime.now(timezone.utc).isoformat(), "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch36_attempt01", "actual_child_invocations": 1, "modules_passed": 0, "module_count_passed": 0, "declarations_passed": 0, "theorems_passed": 0, "definitions_passed": 0, "all_current_bytes_preserved": True, "input_count": 10246, "closed_judge_file_count": 2957, "protected_archive_count": 3089, "capture_count": 125, "axiom_counts": counts, "axiom_rows": rows, "module_evidence": evidence, "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"), "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"), "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"), "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)), "logs_read_scope": "OWN_FULL6d0298", "actual_receipt_read_scope": "OWN_FULLa50f11", "large_PRE_POST_read_scope": "HEADER_PROJECTION91ef5a_PLUS_ALL_ROWS_CURRENT_BYTE_HASHES_NOT_RAW_FULL", "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0, "old_batches_recompiled": False, "author_olean_used": False, "official_modules_before_ROOT_observation": 88, "official_declarations_before_ROOT_observation": 1488, "hypothetical_after_ROOT_modules": 88, "hypothetical_after_ROOT_declarations": 1488, "H1_paid": False, "C5_global_paid": False, "Lambda_tail_paid_by_this_batch": False, "circle_geometry_paid_by_this_batch": False, "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True, "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 0, "declarations_passed": 0, "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"), "axiom_counts": counts, "error_count": 1, "warning_count": 1, "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
