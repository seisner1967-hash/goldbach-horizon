"""Close the unique real batch18 by log metadata and byte hashes only; no compiler."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch18_attempt01"
GATE_SHA = "ce13f703ffb0a7f5c22a214f30e8b5da4606a415ce14c63840eaf93fd0de1c16"
LOG_SHA = "ad9e08512e1a5af905830b98d083925ec8ea4f36c5d01773864c0ca885d2395e"
MODULE = "ThermalGammaMellinInverse22"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def new(path, text):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


def main():
    assert not (OWN / "adjudication.md").exists() and not (OWN / "completion_receipt.json").exists()
    receipt, pre, post, start, fin = [read(ACTUAL / name) for name in
        ("receipt.json", "PREEXEC.json", "POSTEXEC.json", "START.json", "FIN.json")]
    catalog, manifest, old = [read(OWN / name) for name in
        ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json")]
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH18_FAILED"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == len(receipt["rows"]) == 1
    assert receipt["modules_passed"] == receipt["declarations_passed"] == 0
    assert (catalog["module_count"], catalog["total_declarations"], catalog["theorem_count"], catalog["definition_count"]) == (1, 11, 9, 2)
    assert receipt["readonly_local_dependencies"] == ["GammaPrerequisites22"]
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert (len(pre["inputs"]), len(old["inputs"]), len(pre["protected_archives"]), len(pre["captures"])) == (8351, 1109, 3089, 23)
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"], item["source"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == GATE_SHA
    assert receipt["all_current_bytes_preserved"] and post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    row, module = receipt["rows"][0], catalog["modules"][0]
    assert row["module"] == module["module"] == MODULE and row["exit_code"] == 1
    assert row["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL" and not row["timed_out"] and row["launch_error"] is None
    assert read(ACTUAL / (MODULE + "_FIN.json")) == row
    assert row["source_sha256"] == sha(module["source"]) == sha(module["original_source"]) == module["source_sha256"]
    assert row["log_sha256"] == sha(ACTUAL / (MODULE + ".log")) == LOG_SHA
    assert row["olean_sha256"] is None and not list(ACTUAL.glob("*.olean"))
    log = (ACTUAL / (MODULE + ".log")).read_text(encoding="utf-8")
    pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
    parsed = [{"declaration": name, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]}
        for name, values in re.findall(pattern, log, re.S)]
    assert parsed == row["axiom_rows"]
    assert [item["declaration"] for item in parsed] == module["qualified_prints"]
    assert [item["declaration"] for item in parsed] == [item["qualified_name"] for item in module["declarations"]]
    standard = [item for item in parsed if set(item["axioms"]) <= ALLOWED]
    recovery = [item for item in parsed if "sorryAx" in item["axioms"]]
    errors, warnings = len(re.findall(r":\d+:\d+: error:", log)), len(re.findall(r":\d+:\d+: warning:", log))
    assert (len(parsed), len(standard), len(recovery), errors, warnings) == (11, 5, 6, 7, 0)
    assert not row["exact_axiom_coverage_standard_only"]
    assert all(set(item["axioms"]) <= ALLOWED | {"sorryAx"} for item in parsed)
    names = ["START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json",
        MODULE + "_START.json", MODULE + "_FIN.json", MODULE + ".log"]
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Lot18 clos : échec technique, zéro crédit

Une seule tentative réelle6767da/session16697→f44ffc exit1, gate FULL3223b0 SHA {GATE_SHA}, START et dossier actual absents avant lancement. GlobalSTART {start["time_utc"]}, module {row["started_at"]}→{row["finished_at"]}, globalFIN {fin["time_utc"]}. Un seul enfant ThermalGammaMellinInverse22, aucun timeout/retry/probe/ancien compile/numérique/build natif. Source immuable {row["source_sha256"]}. Commande exacte dans START/FIN et reçu ; cwd sources commun, dépendance GammaPrerequisites indépendante readonly, aucun olean auteur et aucune recompilation Gamma. Aucun olean neuf produit.

Log réellement lu FULL3ee55e, SHA {LOG_SHA} ; reçu/globalFIN/moduleFIN FULLd5301a et STARTs FULL9a9fe0. Sept diagnostics : ligne40 composition ContinuousAt.comp infère le mauvais argument g=HAdd.hAdd2 ; deux diagnostics ligne62 abs_of_pos appliqué à ht:t∈Ioi0 sans normalisation/type explicite ; deux diagnostics ligne61 compositions gammaLine∘(±id) non réduites dans les buts ; ligne44 unsolved unknown goal et unknown metavariable sont récupération aval. Ces erreurs demandent des raccords de composition/domaine réel, membership et simplification, sans changer les énoncés. Elles ne sont pas une réfutation analytique ou une obstruction de parité. ROLE3 a reçu les sites et le vrai log pour une éventuelle réparation SOURCE distincte sélectionnée par ROOT.

Couverture observée11prints en ordre exact :5 avec uniquement propext, Classical.choice, Quot.sound ;6 avec sorryAx récupéré. Zéro print vide, zéro avertissement. Les6 déclarations récupérées sont gammaLine_continuous, gammaLine_half_integrable, gammaLine_integrable, expKernel_mellin_vertical_two, mellinInv_Gamma_two et real_exp_eq_Gamma_integral. Les5 prints standards ne deviennent pas un crédit partiel : exit1, aucun olean, zéro module/zéro déclaration acquise. L'inversion réelle complète reste SOURCE non acquise dans ce lot.

Conservation physiquement rehashée :8351inputs/1109 anciens Juge/3089archives/23captures, originaux et copies, gate et dépendance Gamma intacts. PRE SHA {links["PREEXEC.json"]["sha256"]}, POST SHA {links["POSTEXEC.json"]["sha256"]}, actualreceipt SHA {links["receipt.json"]["sha256"]}. GrandsJSON parsés et tous octets liés recontrôlés, aucune prétention rawFULL des milliers de sources d'imports. Lots01–17 et ce lot18 clos sans reprise. Baseline78modules/1304auxiliaires inchangée, observation ROOT encore requise pour la clôture officielle. H1/globalM/C5, coefficientN effectivement calculé, PP/frontière, D_N, Goldbach et WIN restent ouverts. BUILD03 reste une revue SOURCE distincte sans build dans ce rôle ; aucun lot19 préparé automatiquement.
'''
    new(OWN / "adjudication.md", report)
    completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH18", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 0, "declarations_passed": 0, "module_count_passed": 0, "declaration_count_passed": 0,
        "theorems_passed": 0, "definitions_passed": 0, "all_current_bytes_preserved": True, "all_inputs_unchanged": True,
        "input_count": 8351, "closed_judge_file_count": 1109, "protected_archive_count": 3089, "capture_count": 23,
        "print_count": 11, "standard_print_count": 5, "recovery_sorryAx_print_count": 6,
        "declarations_without_axioms": [item["declaration"] for item in parsed if not item["axioms"]],
        "declarations_with_propext_only": [item["declaration"] for item in parsed if item["axioms"] == ["propext"]],
        "warnings": warnings, "errors": errors, "passed_modules": [], "failed_modules": [MODULE], "not_invoked_modules": [],
        "exact_axiom_rows": parsed, "actual_links": links, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "metadata_close_source_sha256": sha(Path(__file__)), "readonly_local_dependencies": ["GammaPrerequisites22"],
        "recompiled_dependencies": [], "old_batches_recompiled": False, "author_olean_used": False, "retry_count": 0,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "previous_official_modules": 78, "previous_official_declarations": 1304,
        "proposed_new_official_modules": 78, "proposed_new_official_declarations": 1304,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False, "C5_paid": False,
        "global_trace_certified": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False,
        "failure_classification": "TECHNICAL_COMPOSITION_MEMBERSHIP_SIMPLIFICATION_RECOVERY",
        "full_log_reads": ["3ee55e"], "full_actual_receipt_read": "d5301a", "full_START_read": "9a9fe0"}
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 0, "declarations_passed": 0,
        "all_current_bytes_preserved": True, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))


if __name__ == "__main__":
    main()
