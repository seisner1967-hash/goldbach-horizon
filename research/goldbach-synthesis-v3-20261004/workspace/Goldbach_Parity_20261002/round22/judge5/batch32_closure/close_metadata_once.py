"""Close real batch32 once: JSON, existing bytes and documentary output only."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
P = B / "round22/judge5/batch32"
A = P / "batch32_attempt01"
G = B / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch32_authorization.json"
MODULE = "ComplexGammaMellinExpTailBridge22"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
DEPENDENCIES = ["GammaPrerequisites22", "ThermalGammaMellinInverse22", "ComplexGammaMellinLocal22", "ComplexGammaMellinHolomorphy22", "ComplexGammaMellinTail22"]


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
checked(G, "c3b57278e72f2262f52d12dd0b2544f800d8f097a1e3d50e1e74d4cf5fb591d3")
checked(A / "receipt.json", "f8f1f0523f6fb245f4e50f8bf7936e499d6061db37d70a3e85b4bef38ba20a65")
checked(P / "catalog.json", "43df009f922ca4c6f03257202f5fae1e869cff4790d357e26ffba9e62017d3f4")
checked(A / "PREEXEC.json", "29a3e3f5d30e9658590df61714770a97b4287e7757962d11abb44aec7139ef3e")
checked(A / "POSTEXEC.json", "e6aa4a38d3e88d51cf395eed834522be1b29a88249a6f9bdc662a6fbbb5b2fdd")
assert gate["authorized"] and gate["attempt"] == "batch32_attempt01"
assert gate["modules"] == [MODULE] and gate["compiler_invocations_maximum"] == 1
assert pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == sha(G)
checked(P / "prepared_manifest.json", gate["source_manifest_sha256"])
checked(P / "run_once.py", gate["launcher_sha256"])
checked(P / "prepared_receipt.json", gate["preparation_receipt_sha256"])
assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH32_AUX_PASS"
assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
assert receipt["modules_passed"] == 1 and receipt["declarations_passed"] == 2
assert all(receipt[key] is False for key in ("author_olean_used", "hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "victory", "D_N_paid"))
assert receipt["numeric_invocations"] == manifest["numeric_invocations"] == 0
assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
assert receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"]
assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
assert len(pre["inputs"]) == receipt["input_count"] == 9787
assert len(pre["captures"]) == receipt["capture_count"] == 109
assert len(pre["protected_archives"]) == receipt["protected_archive_count"] == 3089
assert len(old["inputs"]) == receipt["closed_judge_file_count"] == 2532
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
assert catalog["module_count"] == 1 and catalog["total_declarations"] == 2
assert catalog["theorem_count"] == 2 and catalog["definition_count"] == 0
assert catalog["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == DEPENDENCIES
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
    if dep["module"] in ("ComplexGammaMellinHolomorphy22", "ComplexGammaMellinTail22"):
        assert dep["ROOT_closed_observation_required_and_verified"]

result, module = receipt["rows"][0], catalog["modules"][0]
assert len(receipt["rows"]) == 1 and result["module"] == module["module"] == MODULE
assert not result["timed_out"] and result["launch_error"] is None
assert result["exit_code"] == 0 and result["status"] == "INDEPENDENT_LEAN_AUX_PASS"
assert result["exact_axiom_coverage_standard_only"]
checked(module["source"], result["source_sha256"])
checked(module["original_source"], result["source_sha256"])
checked(A / (MODULE + ".log"), result["log_sha256"])
checked(A / (MODULE + ".olean"), "54edc77d7f7848b55a0a1a36ebec0460e82afd1204b7c5127e80c8a0b344448d")
assert result["olean_sha256"] == sha(A / (MODULE + ".olean"))
log_text = (A / (MODULE + ".log")).read_text(encoding="utf-8-sig")
assert not re.search(r"\b(?:sorryAx|native_decide|ofReduceBool)\b", log_text)
pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
axiom_rows = [{"declaration": name, "axioms": [word.strip() for word in (values or "").replace("\n", " ").split(",") if word.strip()]}
              for name, values in re.findall(pattern, log_text, re.S)]
assert axiom_rows == result["axiom_rows"]
assert [row["declaration"] for row in axiom_rows] == module["qualified_prints"]
assert len(axiom_rows) == len(module["declarations"]) == 2
assert all(set(row["axioms"]) <= STANDARD for row in axiom_rows)
counts = {"standard_triplet": sum(set(row["axioms"]) == STANDARD for row in axiom_rows),
          "empty": sum(not row["axioms"] for row in axiom_rows),
          "recovery": sum("sorryAx" in row["axioms"] for row in axiom_rows)}
assert counts == {"standard_triplet": 2, "empty": 0, "recovery": 0}
errors = re.findall(r"\.lean:(\d+):(\d+): error: ([^\n]*)", log_text)
warning_count = len(re.findall(r"\.lean:\d+:\d+: warning:", log_text))
assert len(errors) == 0 and warning_count == 0
mf, ms = read(A / (MODULE + "_FIN.json")), read(A / (MODULE + "_START.json"))
assert mf == result and start["time_utc"] <= ms["time_utc"] <= result["started_at"] <= result["finished_at"] <= fin["time_utc"]
assert ms["command"] == result["command"] and ms["gate_sha256"] == sha(G)
evidence = [{"module": MODULE, "status": result["status"], "started_at": result["started_at"], "finished_at": result["finished_at"],
             "exit_code": 0, "declarations_passed": 2, "theorems_passed": 2, "definitions_passed": 0,
             "source_sha256": result["source_sha256"], "log_sha256": result["log_sha256"], "olean_sha256": result["olean_sha256"],
             "error_sites": [], "warning_count": warning_count, "axiom_counts": counts,
             "scope": "COMPLEX_GAMMA_EXP_TAIL_BRIDGE_AUX_ONLY"}]
lines = ["# Adjudication indépendante — lot 32", "",
         "Statut réel INDEPENDENT_BATCH32_AUX_PASS : un seul enfant, exit0, olean indépendant produit, zéro reprise. Catalogue exact : deux théorèmes, zéro définition, deux impressions qualifiées dans leur ordre exact.", "",
         f"START global {start['time_utc']}, FIN global {fin['time_utc']} ; parent38454d/session13127→dcc06d exit0. TOOL_START2026-10-04T02:06:59.6703598Z, TOOL_FIN2026-10-04T02:07:36.5695941Z. Module START {result['started_at']}, FIN {result['finished_at']}. Aucun timeout ni erreur de lancement.", "",
         "Journal intégral FULL0d59c3, reçu FULLd3d2d3, START FULLc08aa9, FIN FULLcfa728, moduleSTART/FIN FULL52fa7e. Zéro erreur, zéro avertissement. Audit des deux axiomes : deux triplets [propext, Classical.choice, Quot.sound], zéro liste vide et zéro récupération sorryAx. Aucun axiome personnalisé, sorry, admit ou mécanisme natif contribue à ces déclarations.", "",
         "Portée mathématique acquise : pour Re(w)>0 et H≥0, exp(-w)-complexGammaTruncated(w,H)=complexGammaTail(w,H), puis norme de cette différence≤complexGammaTailRadius(w,H). Les preuves substituent l'identité réellement certifiée complexGammaInverse_eq_exp de Holo27 dans les deux conclusions certifiées de Tail30. Le rayon réel R=C exp(-δH)/(πδ) et les intégrabilités sont construits dans les dépendances acquises ; aucune conclusion finale ou intégrabilité libre n'est offerte en prémisse du bridge.", "",
         "La source et son catalogue historique pending restent byte-identiques. Leur ancien commentaire Tail28/SOURCE02 ne remplace pas la provenance réelle : le staging utilise Holo27 et Tail03 PASS30. Gamma02/Thermal20/Local26/Holo27/Tail30 sont les cinq dépendances readonly ; Local26 conserve globalFAILED mais sa ligne PASS22 et la clôture ROOT partielle sont vérifiées. Les véritables FIN/logs/reçus, sources/oleans originaux et copies sont conservés, sans recompilation ancienne ni olean auteur.", "",
         "Conservation physique après FIN :9787 inputs,2532 anciens fichiers Juge,3089 archives et109 captures original/copie rehashés intacts. PRE/POST concordent exactement, sources/gate/oleans readonly inchangés. La clôture n'exécute que JSON/SHA et écrit ces deux pièces documentaires. Zéro Lean, candidat, numérique ou exécutable natif dans la clôture. Les nouveaux outils SOURCE33 sont hors du snapshot32, sans modification d'anciens fichiers protégés.", "",
         "Baseline officielle avant observation ROOT :86 modules/1456 déclarations. Ajout admissible après observation physique ROOT seulement :1 module/2 théorèmes, soit hypothétiquement87/1458. Le mainΛ FAILED31 et sa réparation SOURCE02, EΛ16, Geometry25, ζ/Weil, compte/queue des zéros, annulation signée, PP/front, coefficientN=10^8, D_N et WIN restent hors de ce PASS.", "",
         f"Reçu réel {A / 'receipt.json'} SHA {sha(A / 'receipt.json')}.",
         f"PRE {sha(A / 'PREEXEC.json')} ; POST {sha(A / 'POSTEXEC.json')}.",
         f"Source {result['source_sha256']} ; log {result['log_sha256']} ; olean {result['olean_sha256']}.", ""]
write_new(P / "adjudication.md", "\n".join(lines) + "\n")
completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH32", "time_utc": datetime.now(timezone.utc).isoformat(),
              "status": receipt["status"], "actual_status": receipt["status"], "attempt": "batch32_attempt01",
              "actual_child_invocations": 1, "modules_passed": 1, "module_count_passed": 1,
              "declarations_passed": 2, "theorems_passed": 2, "definitions_passed": 0,
              "all_current_bytes_preserved": True, "input_count": 9787, "closed_judge_file_count": 2532,
              "protected_archive_count": 3089, "capture_count": 109, "axiom_counts": counts,
              "axiom_rows": axiom_rows, "module_evidence": evidence,
              "actual_receipt_path": str(A / "receipt.json"), "actual_receipt_sha256": sha(A / "receipt.json"),
              "adjudication_sha256": sha(P / "adjudication.md"), "PREEXEC_sha256": sha(A / "PREEXEC.json"),
              "POSTEXEC_sha256": sha(A / "POSTEXEC.json"), "START_sha256": sha(A / "START.json"), "FIN_sha256": sha(A / "FIN.json"),
              "gate_sha256": sha(G), "metadata_helper_sha256": sha(Path(__file__)),
              "logs_read_scope": "FULL0d59c3", "actual_receipt_read_scope": "FULLd3d2d3",
              "module_START_FIN_read_scope": "FULL52fa7e plus exact equality to receipt row",
              "large_PRE_POST_read_scope": "CONTROL_HEADER_PLUS_ALL_JSON_ROWS_AND_CURRENT_BYTE_HASH_NOT_RAW_FULL",
              "compiler_invocations_in_closure": 0, "numeric_invocations": 0, "produced_binary_calls": 0,
              "old_batches_recompiled": False, "author_olean_used": False,
              "official_modules_before_ROOT_observation": 86, "official_declarations_before_ROOT_observation": 1456,
              "hypothetical_after_ROOT_modules": 87, "hypothetical_after_ROOT_declarations": 1458,
              "H1_paid": False, "C5_global_paid": False, "exp_bridge_paid_by_this_module": True,
              "Lambda_weighted_tail_paid": False, "native_refinement_paid": False,
              "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
write_new(P / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": completion["status"], "all_current_bytes_preserved": True,
                  "actual_receipt_sha256": completion["actual_receipt_sha256"], "modules_passed": 1, "declarations_passed": 2,
                  "adjudication_sha256": sha(P / "adjudication.md"), "completion_sha256": sha(P / "completion_receipt.json"),
                  "axiom_counts": counts, "error_count": len(errors), "warning_count": warning_count,
                  "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
