"""Close the real batch17: hashes and compiler-log metadata only."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch17_attempt01"
GATE_SHA = "aeb0c7cd93e90ab54acb932f02d8b904f93b72bd912109eec27808c5fd09188b"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))

def new(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(value)

def main():
    assert not (OWN / "adjudication.md").exists() and not (OWN / "completion_receipt.json").exists()
    receipt, pre, post, start, fin = [read(ACTUAL / name) for name in ("receipt.json", "PREEXEC.json", "POSTEXEC.json", "START.json", "FIN.json")]
    catalog, manifest, old = [read(OWN / name) for name in ("catalog.json", "prepared_manifest.json", "closed_judge_bindings.json")]
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH17_AUX_PASS"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == len(receipt["rows"]) == 2
    assert receipt["modules_passed"] == 2 and receipt["declarations_passed"] == 52
    assert catalog["module_count"] == 2 and catalog["total_declarations"] == 52
    assert catalog["theorem_count"] == 32 and catalog["definition_count"] == 20
    assert receipt["readonly_local_dependencies"] == []
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 8160 and len(old["inputs"]) == 1054
    assert len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 24
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"], item["source"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == GATE_SHA
    assert receipt["all_current_bytes_preserved"] and post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    audits = []
    errors = warnings = 0
    expected_logs = ["855ac68e1887a2a719e9edee0f4a7040fad077ac78b64eafb6ee81fb99a43c9c", "39cd23d7b62c3123cf2063826717aea72117cb9a2b3c99c9d1e4507738589f93"]
    expected_oleans = ["20db07cdfb5717d7f9ab0b3e75d3c15b9e16c6820ad5285bd7debb62b0a31434", "e821070b97b3fa4b71a3e279ecb9bc6c0de6cafdfe9dc8712b5d5a22858a6485"]
    for index, (row, module) in enumerate(zip(receipt["rows"], catalog["modules"])):
        name = module["module"]
        assert row["module"] == name and row["exit_code"] == 0 and row["status"] == "INDEPENDENT_LEAN_AUX_PASS"
        assert not row["timed_out"] and row["launch_error"] is None and row["exact_axiom_coverage_standard_only"]
        assert read(ACTUAL / (name + "_FIN.json")) == row
        assert row["source_sha256"] == sha(module["source"]) == sha(module["original_source"]) == module["source_sha256"]
        assert row["log_sha256"] == sha(ACTUAL / (name + ".log")) == expected_logs[index]
        assert row["olean_sha256"] == sha(ACTUAL / (name + ".olean")) == expected_oleans[index]
        log = (ACTUAL / (name + ".log")).read_text(encoding="utf-8")
        raw = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)
        parsed = [{"declaration": declaration, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]} for declaration, values in raw]
        assert parsed == row["axiom_rows"]
        assert [item["declaration"] for item in parsed] == module["qualified_prints"]
        assert [item["declaration"] for item in parsed] == [item["qualified_name"] for item in module["declarations"]]
        assert all(set(item["axioms"]) <= ALLOWED for item in parsed)
        assert not any(token in log for token in ("sorryAx", "Lean.ofReduceBool", "native_decide"))
        errors += len(re.findall(r":\d+:\d+: error:", log))
        warnings += len(re.findall(r":\d+:\d+: warning:", log))
        audits.extend(parsed)
    empty = [item["declaration"] for item in audits if not item["axioms"]]
    propext_only = [item["declaration"] for item in audits if item["axioms"] == ["propext"]]
    assert len(audits) == 52 and errors == 0 and warnings == 6
    assert empty == ["GoldbachLogQuantization22.clampInteger"]
    assert propext_only == ["GoldbachLogQuantization22.gridScale", "GoldbachLogQuantization22.reductionExponent", "GoldbachLogQuantization22.clampInteger_bounds"]
    assert len(list(ACTUAL.glob("*.olean"))) == 2
    names = ["START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json"]
    for row in receipt["rows"]:
        names.extend(row["module"] + suffix for suffix in ("_START.json", "_FIN.json", ".log", ".olean"))
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Lot 17 clos : PASS indépendant de deux auxiliaires

Une seule tentative réelle 17728e/session24652→0500a6 exit0 ; gate lue FULL7872a7 SHA {GATE_SHA}, START préalable absent. Global START {start["time_utc"]}, FIN {fin["time_utc"]}. RationalLogQuantization22 : {receipt["rows"][0]["started_at"]}→{receipt["rows"][0]["finished_at"]}, exit0 ; QuantizedLambdaEnvelope22 : {receipt["rows"][1]["started_at"]}→{receipt["rows"][1]["finished_at"]}, exit0. Deux enfants seulement, sans retry/probe/recompilation ancienne/numérique. Le second import utilise exclusivement le premier olean indépendant neuf dans la racine commune, aucun olean auteur. Commandes exactes dans les deux START/FIN et le reçu.

Couverture exacte :38+14=52 déclarations,32 théorèmes+20 définitions, tous prints en ordre identique au catalogue. Zéro erreur ; six avertissements linter unnecessarySeqFocus dans Rational, aucun avertissement dans Envelope. Aucun sorryAx/recovery/native_decide/axiome non standard. clampInteger est la seule déclaration sans axiome ; gridScale, reductionExponent et clampInteger_bounds dépendent seulement de propext ; les48 autres dépendent exactement de propext, Classical.choice et Quot.sound. Logs réellement lus FULLc05248 et FULL916902 ; reçu/globalFIN/deuxSTART FULL ee2407 ; catalogue FULLfa3179.

Portée acquise : la vraie série logarithmique, sa réduction et sa queue à32 termes construisent l'encloser rationnel ; nearestEven puis clamp donnent le constructeur canonique avec erreur ≤1/S, S=2^58, pour2≤p≤10^8. Le second module utilise la vraie Λ, conserve les puissances premières et traite0/1 séparément ; précision des poids, erreur des produits et de la somme, normalisation entière, enveloppe E=(N+1)(64/S+1/S²) continue pour s>0 et garde tau fixe sont démontrées. Aucune précision finale libre ni majorant du coefficient supposé : ce sont les constructions auditées SOURCE dans les revues revision02/03, désormais compilées. Les corrections de raccords FAIL16 sont payées ; ce lot ne rejoue pas16 et aucune obstruction de parité n'est attribuée aux anciens diagnostics.

Sources immuables dfabcabf39ecc1ba7769eb99ea73e0483dc6925f0bb3d11c05891d22c0a787a7 et526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331. Logs SHA {expected_logs[0]} / {expected_logs[1]}. Ole ans indépendants SHA {expected_oleans[0]} / {expected_oleans[1]}.

Conservation physiquement rehashée :8160inputs/1054 anciens Juge/3089archives/24captures, originaux et copies, et gate intacts. PRE {links["PREEXEC.json"]["sha256"]}, POST {links["POSTEXEC.json"]["sha256"]}, receipt {links["receipt.json"]["sha256"]}. Les grands JSON ont été parsés et tous octets liés vérifiés ; ceci ne prétend pas rawFULL du texte intégral des imports. Les lots01–16 restent clos readonly. Baseline officielle76/1252 jusqu'à observation ROOT ; proposition limitée78/1304 auxiliaires. Construction canonique native en C++/catalogue/word-arithmetic/NTT/CRT et coefficientN à10^8 effectivement calculé restent à certifier et exécuter ; aucun programme natif construit ni nouveau banc ici. H1global/C5global, séparation PP/frontière, D_N, Goldbach et WIN restent ouverts. Aucun batch18 ni build natif automatiquement préparé.
'''
    report = report.replace("Ole ans", "Oleans")
    new(OWN / "adjudication.md", report)
    completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH17", "time_utc": datetime.now(timezone.utc).isoformat(), "status": receipt["status"], "role": "ROLE5",
        "actual_child_invocations": 2, "modules_passed": 2, "declarations_passed": 52, "module_count_passed": 2, "declaration_count_passed": 52,
        "theorems_passed": 32, "definitions_passed": 20, "all_current_bytes_preserved": True, "all_inputs_unchanged": True,
        "input_count": 8160, "closed_judge_file_count": 1054, "protected_archive_count": 3089, "capture_count": 24,
        "print_count": 52, "standard_print_count": 52, "recovery_sorryAx_print_count": 0, "declarations_without_axioms": empty,
        "declarations_with_propext_only": propext_only, "warnings": 6, "errors": 0,
        "passed_modules": [row["module"] for row in receipt["rows"]], "failed_modules": [], "not_invoked_modules": [],
        "exact_axiom_rows": audits, "actual_links": links, "adjudication_sha256": sha(OWN / "adjudication.md"), "metadata_close_source_sha256": sha(Path(__file__)),
        "readonly_local_dependencies": [], "recompiled_dependencies": [], "old_batches_recompiled": False, "author_olean_used": False, "retry_count": 0,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False, "previous_official_modules": 76, "previous_official_declarations": 1252,
        "proposed_new_official_modules": 78, "proposed_new_official_declarations": 1304, "official_count_requires_ROOT_observation": True,
        "H1_paid": False, "C5_paid": False, "global_trace_certified": False, "coefficient_N_computed": False, "D_N_paid": False, "WIN": False,
        "full_log_reads": ["c05248", "916902"], "full_actual_receipt_read": "ee2407", "full_START_read": "e59907", "full_module_START_reads": "ee2407"}
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 2, "declarations_passed": 52, "all_current_bytes_preserved": True,
        "adjudication_sha256": sha(OWN / "adjudication.md"), "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))

if __name__ == "__main__":
    main()
