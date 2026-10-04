"""One documentary closure of real AUX_PASS35; JSON/byte hashes only."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch35"
A = P / "batch35_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch35_authorization.json"
MODULE = "ComplexGammaMellinLambda22"
DEPS = ["GammaPrerequisites22", "ThermalGammaMellinInverse22", "ComplexGammaMellinLocal22", "ComplexGammaMellinHolomorphy22"]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PINS = {
    G: "6c92ce5237994127e456ac90a56311b8243d0e0cf759ce53af53721237c29471",
    A / "receipt.json": "3cffa331b39283808678dbfa5dc36081f4e5a2698c8a9f278d6b8b6a63ec6832",
    A / "PREEXEC.json": "118d73e0af3f43b125c313fd052bf6c91106fc96ea72f392058413597bd9ef7f",
    A / "POSTEXEC.json": "6f870c01d78f1083ad0e9c4f1a76f09535a15bcde727404909b71764bbdbcc2b",
    A / (MODULE + ".log"): "292d617a82ff8d5afd1a99a07a05673f09aa09f19fab237bc87206cbdae27b75",
    A / (MODULE + ".olean"): "8b557d2ccc8f8f6efbf5a33147aca94e12a3d7b2fcdd095af9024ffb492777c5",
    P / "catalog.json": "3502fe72c4fbe82c7fbbd5fcf4b6577e5404b665f82ad0e751d41860e309d902",
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
assert gate["authorized"] and gate["attempt"] == "batch35_attempt01" and gate["modules"] == [MODULE]
assert gate["compiler_invocations_maximum"] == 1 and gate["prior_modules"] == 87 and gate["prior_declarations"] == 1458
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH35_AUX_PASS"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == 1 and receipt["declarations_passed"] == 30
assert all(receipt[key] is False for key in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == len(manifest["immutable_inputs"]) == receipt["input_count"] == 10092
assert len(pre["captures"]) == receipt["capture_count"] == 103
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 2819
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
assert result["exit_code"] == 0 and result["status"] == "INDEPENDENT_LEAN_AUX_PASS"
assert not result["timed_out"] and result["launch_error"] is None and result["exact_axiom_coverage_standard_only"]
checked(A / (MODULE + ".olean"), result["olean_sha256"], 498944)
checked(module["source"], result["source_sha256"])
checked(module["original_source"], result["source_sha256"])
log_text = (A / (MODULE + ".log")).read_text(encoding="utf-8-sig")
pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
axiom_rows = [{"declaration": name, "axioms": [word.strip() for word in (values or "").replace("\n", " ").split(",") if word.strip()]} for name, values in re.findall(pattern, log_text, re.S)]
assert axiom_rows == result["axiom_rows"] and [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == len({row["declaration"] for row in axiom_rows}) == 30
assert all(set(row["axioms"]) == STANDARD and len(row["axioms"]) == len(set(row["axioms"])) for row in axiom_rows)
assert not re.search(r"\b(?:sorryAx|native_decide|ofReduceBool)\b", log_text)
counts = {"standard_triplet": 30, "empty": 0, "recovery": 0}
errors = re.findall(r"\.lean:(\d+):(\d+): error: ([^\n]*)", log_text)
warnings = re.findall(r"\.lean:(\d+):(\d+): warning: ([^\n]*)", log_text)
assert errors == [] and warnings == [("185", "62", "unused variable `hw`")]
mf, ms = read(A / (MODULE + "_FIN.json")), read(A / (MODULE + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = [{"module": MODULE, "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"], "exit_code": 0, "declarations_passed": 30, "theorems_passed": 24, "definitions_passed": 6, "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": result["olean_sha256"], "error_sites": errors, "warning_count": 1, "axiom_counts": counts, "scope": "TRUE_LAMBDA_COMPLEX_GAMMA_MELLIN_AUX_ONLY"}]
lines = ["# Adjudication indépendante — lot 35", "", "Statut réel INDEPENDENT_BATCH35_AUX_PASS : une compilation neuve, exit0, olean produite, aucun timeout ni reprise. Module entier validé :24 théorèmes/6 définitions/30 déclarations auxiliaires. Attribution officielle encore soumise à l'observation ROOT.", "", f"Parent afd5e3/session15715→91dab1 exit0. TOOL_START2026-10-04T03:18:34.2396312Z, TOOL_FIN2026-10-04T03:19:47.4337788Z. START global {start['time_utc']}, FIN global {fin['time_utc']}; module {result['started_at']}→{result['finished_at']}.", "", "Log réellement lu FULL83477f, receipt FULL8e0497, START/FIN/hashes FULL463ba6. Zéro erreur ; seul avertissement185:62 hw inutilisé. Aucun rerun pour le linter. Le cas zéro corrigé par he/funext/map_zero puis rw est maintenant élaboré ; aucune recovery sorryAx. Les FAIL31 et33 restent archivés séparément sans reprise.", "", "Couverture indépendante : les30 noms du catalogue dans l'ordre exact,30 triplets [propext,Classical.choice,Quot.sound],0 liste vide,0 récupération. Aucun axiome personnalisé ou mécanisme natif dans ces prints. SOURCE4a944… intacte, aucun sorry/admit/axiom/native_decide/unsafe introduit. La nouvelle olean est8b557d2ccc8f8f6efbf5a33147aca94e12a3d7b2fcdd095af9024ffb492777c5.", "", "Portée effectivement élaborée : vraie Λ (toutes les puissances premières conservées), Q=ΣΛ(n)n^−2≤6, norme et continuité de D(t), intégrabilités et domination locale construites, branche principale sur Re(w)>0, inversion terme à terme puis échange infini donnant P(w)=(1/(2π))∫D(t)Γ(2+it)w^(−2−it)dt. Aucune L1/égalité/borne finale n'est offerte en prémisse. La revue scientifique SOURCE03 indépendante9c2e25… et les énoncés réellement compilés fondent cette portée limitée.", "", "Γ02/Thermal20/Local26/Holo27 restent quatre dépendances indépendantes readonly, sans recompilation ni olean auteur. Local26 garde sa rowPASS22 malgré le lot globalFAILED et son observation ROOT partielle. Aucun import Tail/bridge/EΛ/Geometry/coefficient dans main35.", "", "Conservation physique indépendante après FIN :10092 inputs,2819 anciens fichiers Juge,3089 archives et103 captures source/copie rehashés intacts. PRE/POST concordent ; sources, gate et dépendances immuables, dont FAIL33 et six DRAFT34. Clôture exclusivement JSON/SHA et deux pièces documentaires, zéro nouvelle compilation ou calcul numérique.", "", "Baseline officielle87/1458 avant observation ROOT ; seul incrément envisageable après cette observation :1/30, donc88/1488. Les queues pondérées et leur géométrie, ζ/Weil, annulation signée canonique, correction PP/front, coefficient effectifN=10^8, H1/globalC5/D_N/WIN ne sont pas acquis par ce lot.", "", f"Receipt {sha(A / 'receipt.json')}; PRE {sha(A / 'PREEXEC.json')}; POST {sha(A / 'POSTEXEC.json')}; log {result['log_sha256']}.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH35", "time_utc": datetime.now(timezone.utc).isoformat(), "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch35_attempt01", "actual_child_invocations": 1, "modules_passed": 1, "module_count_passed": 1, "declarations_passed": 30, "theorems_passed": 24, "definitions_passed": 6, "all_current_bytes_preserved": True, "input_count": 10092, "closed_judge_file_count": 2819, "protected_archive_count": 3089, "capture_count": 103, "axiom_counts": counts, "axiom_rows": axiom_rows, "module_evidence": evidence, "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"), "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"), "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"), "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)), "logs_read_scope": "FULL83477f", "actual_receipt_read_scope": "FULL8e0497", "module_START_FIN_read_scope": "FULL9c47e0/463ba6 plus FIN exact equality to real receipt row", "large_PRE_POST_read_scope": "ALL_METADATA_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL", "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0, "old_batches_recompiled": False, "author_olean_used": False, "official_modules_before_ROOT_observation": 87, "official_declarations_before_ROOT_observation": 1458, "hypothetical_after_ROOT_modules": 88, "hypothetical_after_ROOT_declarations": 1488, "H1_paid": False, "C5_global_paid": False, "Lambda_Mellin_paid_by_this_module": True, "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True, "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 1, "declarations_passed": 30, "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"), "axiom_counts": counts, "error_count": 0, "warning_count": 1, "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
