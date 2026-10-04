"""Metadata closure only for the unique already-finished independent batch21. No compiler or candidate import."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json

OWN = Path(__file__).resolve().parent
BASE = OWN.parents[2]
PREP = BASE / "round22/role4/concrete_ntt_roots_prepare21"
DOC = PREP  # ROOT explicitly selected these two new documentary output paths after the real FIN.
ACT = PREP / "batch21_attempt01"
GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge5_batch21_authorization.json"

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def write_new(path, data):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(data, stream, ensure_ascii=False, indent=2, sort_keys=True)
        stream.write("\n")

def main():
    need(not (DOC / "completion_receipt.json").exists() and not (DOC / "adjudication.md").exists(), "CLOSURE_EXISTS")
    receipt = read(ACT / "receipt.json")
    pre, post = read(ACT / "PREEXEC.json"), read(ACT / "POSTEXEC.json")
    manifest, catalog = read(PREP / "prepared_manifest.json"), read(PREP / "catalog.json")
    need(receipt["status"] == "INDEPENDENT_BATCH21_FAILED" and receipt["actual_child_invocations"] == 1, "ACTUAL_STATUS")
    need(receipt["modules_passed"] == receipt["declarations_passed"] == 0, "ZERO_CREDIT")
    need(receipt["input_count"] == 8380 and receipt["closed_judge_file_count"] == 1268 and receipt["protected_archive_count"] == 3089, "COUNTS")
    need(receipt["capture_count"] == 35 and receipt["all_current_bytes_preserved"] and receipt["all_inputs_unchanged"], "ACTUAL_CONSERVATION")
    need(len(manifest["immutable_inputs"]) == len(pre["inputs"]) == len(post["inputs"]) == 8380, "INPUT_COUNTS")
    need(pre["inputs"] == post["inputs"], "PRE_POST_INPUTS")
    expected = {row["path"]: row["sha256"] for row in manifest["immutable_inputs"]}
    need(len(expected) == 8380 and expected == {row["path"]: row["sha256"] for row in pre["inputs"]}, "MANIFEST_PRE")
    for row in manifest["immutable_inputs"]:
        need(sha(row["path"]) == row["sha256"], "CURRENT_INPUT:" + row["path"])
        if "bytes" in row:
            need(Path(row["path"]).stat().st_size == row["bytes"], "INPUT_SIZE:" + row["path"])
    registry = read(BASE / "round22/previous_artifacts_sha256.json")
    need(registry["file_count"] == len(registry["sha256"]) == 3089, "REGISTRY_COUNT")
    need(pre["protected_archives"] == post["protected_archives"], "PRE_POST_ARCHIVES")
    need({row["path"]: row["sha256"] for row in pre["protected_archives"]} == registry["sha256"], "REGISTRY_PRE")
    for relative, digest in registry["sha256"].items():
        need(sha(BASE / relative) == digest, "CURRENT_ARCHIVE:" + relative)
    need(len(pre["captures"]) == 35, "CAPTURE_COUNT")
    for row in pre["captures"]:
        need(sha(row["source"]) == row["sha256"] == sha(row["capture"]), "CURRENT_CAPTURE:" + row["source"])
    need(sha(GATE) == pre["gate_sha256"] == post["gate_sha256"] == "0bd75051f583fe97c68a39433851332ac6f90322f9f2a980b13d03333bc5c7fe", "GATE")
    need(post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"], "POST_FLAGS")
    row = receipt["rows"][0]
    need(row["module"] == "ConcreteNTTRoots22" and row["exit_code"] == 1 and row["olean_sha256"] is None and not row["timed_out"], "ROOTS_REAL_FAIL")
    log_path = ACT / "ConcreteNTTRoots22.log"
    need(sha(log_path) == row["log_sha256"] == "ff1a8a6604d45cf2ad3336ef8b433c33b974f7766845c9411c29d68dd04e399f", "LOG_HASH")
    log = log_path.read_text(encoding="utf-8")
    need(log.count(": error:") == 16 and log.count(": warning:") == 0, "DIAGNOSTIC_COUNTS")
    axioms = row["axiom_rows"]
    need([item["declaration"] for item in axioms] == catalog["modules"][0]["qualified_prints"] and len(axioms) == 18, "EXACT_PRINTS")
    sorry_rows = [item for item in axioms if "sorryAx" in item["axioms"]]
    standard_rows = [item for item in axioms if "sorryAx" not in item["axioms"]]
    need(len(sorry_rows) == 10 and len(standard_rows) == 8 and all(item["axioms"] for item in axioms), "AXIOM_COUNTS")
    need(standard_rows[0]["declaration"] == "GoldbachConcreteNTTRoots22.bankRoot" and standard_rows[0]["axioms"] == ["propext", "Quot.sound"], "ROOT_DEF_AXIOMS")
    need(all(set(item["axioms"]) == {"propext", "Classical.choice", "Quot.sound"} for item in standard_rows[1:]), "OTHER_STANDARD_AXIOMS")
    for module in ("ConcreteNTTRoots22", "ConcreteNTTA32Projection22"):
        need(not (ACT / (module + ".olean")).exists(), "NO_OLEAN:" + module)
    for suffix in ("_START.json", "_FIN.json", ".log"):
        need(not (ACT / ("ConcreteNTTA32Projection22" + suffix)).exists(), "BRIDGE_NOT_INVOKED")
    artifacts = {name: {"path": str(ACT / name), "sha256": sha(ACT / name)} for name in (
        "START.json", "FIN.json", "ConcreteNTTRoots22_START.json", "ConcreteNTTRoots22_FIN.json", "ConcreteNTTRoots22.log", "PREEXEC.json", "POSTEXEC.json", "receipt.json")}
    report = f"""# Adjudication indépendante batch21 — FAIL technique, zéro crédit

Unique parent canonical Python -I -S -B -X utf8 ; exécution daff30/session35009 puis FIN46921e exit1. Gate et launcher lus FULL93cb32, bindings/absence initiale c94f5b ; aucune reprise. START global20:26:43.455989UTC ; Roots {row['started_at']}→{row['finished_at']} exit1 ; FIN global20:27:02.635378UTC. Commande : Lean4.15 -DmaxHeartbeats=1000000 -o [olean exclusif] [source433903d4…] ; common cwd sources, trois oleans indépendants19/17 readonly seulement.

Roots échoue sur16 buts False après normalisation partielle de val : lignes47/51/55,70/74,87/91,104/108,121/125,137/149/161/173/185. Le log laisse hv : ZMod.val <numéral résiduel> = 1 ; les simp/norm_num de val_natCast ne ferment pas ces expressions numériques. Aucune réfutation d'identité ni obstruction de parité n'est observée. Ce raccord OfNat/val nécessite une révision SOURCE distincte et une nouvelle gate ; aucun correctif ni nouveau compiler exécuté ici.

18 prints Roots présents dans l'ordre exact : bankRoot dépend de propext/Quot.sound ;7 autres déclarations standard ont propext/Classical.choice/Quot.sound ;5 primalités et5 racines portent sorryAx généré par recovery. Zéro déclaration sans axiomes. Aucun olean ; le module entier reçoit zéro crédit. Bridge10 est NON_INVOKED, sans START/FIN/log/olean, conformément au premier échec. Le lot visait28=22thm6defs, aucun des28 n'est crédité.

Log/receipt/FIN réellement lus FULLf900fb ; log SHA{row['log_sha256']}. Clôture metadata indépendante :8380 inputs,1268 anciensJuge inclus,3089 archives et35 captures originales/copies physiquement rehashés intacts ; PRE/POST et gate concordants. Les trois dépendances readonly restent intactes, zéro ancienne compilation ou bank replay. Le grand manifeste est traité en totalité comme métadonnées+bytes, sans prétendre RAW_FULL des milliers de sources imports.

Status INDEPENDENT_BATCH21_FAILED ; modules_passed=0, declarations_passed=0, all_current_bytes_preserved=true. Baseline ROOT80/1339 inchangée, aucun PASS global/H1/coefficientN/D_N/WIN. Les anciens lots et sources auteur restent gelés.
"""
    with (DOC / "adjudication.md").open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(report)
    completion = {"schema": "ROUND22_JUDGE5_BATCH21_COMPLETION", "status": receipt["status"],
        "time_utc": datetime.now(timezone.utc).isoformat(), "attempt": "batch21_attempt01",
        "actual_child_invocations": 1, "modules_passed": 0, "declarations_passed": 0,
        "all_current_bytes_preserved": True, "inputs_verified": 8380, "old_judge_files_verified": 1268,
        "archives_verified": 3089, "captures_verified": 35, "standard_axiom_prints": 8,
        "recovery_sorryAx_prints": 10, "empty_axiom_prints": 0, "exact_print_order": True,
        "Lean_errors": 16, "Lean_warnings": 0, "modules_not_invoked": ["ConcreteNTTA32Projection22"],
        "prior_modules": 80, "prior_declarations": 1339, "proposed_modules": 80, "proposed_declarations": 1339,
        "actual_receipt_path": str(ACT / "receipt.json"), "actual_receipt_sha256": sha(ACT / "receipt.json"),
        "adjudication_path": str(DOC / "adjudication.md"), "adjudication_sha256": sha(DOC / "adjudication.md"),
        "artifacts": artifacts, "candidate_or_compiler_invocations_in_closure": 0,
        "retry_count": 0, "old_batches_recompiled": False, "numeric_bank_replayed": False,
        "H1_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False}
    write_new(DOC / "completion_receipt.json", completion)
    print(json.dumps({"status": completion["status"], "adjudication_sha256": completion["adjudication_sha256"],
        "completion_sha256": sha(DOC / "completion_receipt.json"), "modules_passed": 0,
        "declarations_passed": 0, "all_current_bytes_preserved": True}, sort_keys=True))

if __name__ == "__main__":
    main()
