"""Close unique actual20 with log metadata and byte hashes only; no compiler."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch20_attempt01"
MODULE = "ThermalGammaMellinInverse22"
GATE_SHA = "8bbe8f7a6989da179664a06b223261dfe947117f8efb328a53849ad334b531c6"
LOG_SHA = "5eaeb84674dccd75b3b651543960a077f0ab31d5a338eab19302945be0790eac"
OLEAN_SHA = "e9442776bb512a4f83391b63402a1dc86bce61070dfc386bc8b6873af521ce24"
DEPS = ["GammaPrerequisites22"]
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
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH20_AUX_PASS"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == len(receipt["rows"]) == 1
    assert (receipt["modules_passed"], receipt["declarations_passed"]) == (1, 11)
    assert (catalog["module_count"], catalog["total_declarations"], catalog["theorem_count"], catalog["definition_count"]) == (1, 11, 9, 2)
    assert receipt["readonly_local_dependencies"] == DEPS
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert (len(pre["inputs"]), len(old["inputs"]), len(pre["protected_archives"]), len(pre["captures"])) == (8456, 1214, 3089, 27)
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"], item["source"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"] == GATE_SHA
    assert receipt["all_current_bytes_preserved"] and post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    row, module = receipt["rows"][0], catalog["modules"][0]
    assert row["module"] == module["module"] == MODULE and row["exit_code"] == 0
    assert row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and not row["timed_out"] and row["launch_error"] is None
    assert read(ACTUAL / (MODULE + "_FIN.json")) == row
    assert row["source_sha256"] == sha(module["source"]) == sha(module["original_source"]) == module["source_sha256"]
    assert row["log_sha256"] == sha(ACTUAL / (MODULE + ".log")) == LOG_SHA
    assert row["olean_sha256"] == sha(ACTUAL / (MODULE + ".olean")) == OLEAN_SHA
    assert [path.name for path in ACTUAL.glob("*.olean")] == [MODULE + ".olean"]
    for dep in catalog["dependency_bindings"]:
        assert sha(dep["source"]) == dep["source_sha256"]
        assert sha(dep["olean_original"]) == sha(dep["olean_copy"]) == dep["olean_sha256"]
        assert sha(dep["independent_receipt"]) == dep["independent_receipt_sha256"]
    log = (ACTUAL / (MODULE + ".log")).read_text(encoding="utf-8")
    pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
    parsed = [{"declaration": name, "axioms": [v.strip() for v in (values or "").replace("\n", " ").split(",") if v.strip()]}
        for name, values in re.findall(pattern, log, re.S)]
    assert parsed == row["axiom_rows"]
    assert [item["declaration"] for item in parsed] == module["qualified_prints"]
    assert [item["declaration"] for item in parsed] == [item["qualified_name"] for item in module["declarations"]]
    assert all(set(item["axioms"]) <= ALLOWED for item in parsed)
    assert not re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", log)
    errors, warnings = len(re.findall(r":\d+:\d+: error:", log)), len(re.findall(r":\d+:\d+: warning:", log))
    empty = [item["declaration"] for item in parsed if not item["axioms"]]
    prop = [item["declaration"] for item in parsed if item["axioms"] == ["propext"]]
    assert (len(parsed), len(empty), len(prop), errors, warnings) == (11, 0, 0, 0, 0)
    assert prop == []
    assert row["exact_axiom_coverage_standard_only"]
    names = ["START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json",
        MODULE + "_START.json", MODULE + "_FIN.json", MODULE + ".log", MODULE + ".olean"]
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Lot20 clos : PASS indépendant Γ Mellin11

Unique exécution a58a27/session20281→9a0847 exit0, gate FULL6d61ef SHA {GATE_SHA}, dossier et START absents avant lancement. GlobalSTART {start["time_utc"]}, module {row["started_at"]}→{row["finished_at"]}, globalFIN {fin["time_utc"]}. Un seul enfant ThermalGammaMellinInverse22, aucun timeout/retry/probe/ancien compile/numeric/native build. Commande réelle en START/FIN/reçu, racine sources unique, GammaPrerequisites22 indépendant PASS02 readonly sans recompilation, aucun olean auteur. Source {row["source_sha256"]} immuable ; nouvel olean indépendant SHA {OLEAN_SHA}.

Log, reçu et globalFIN lus FULLaadc49 ; STARTs FULL32c370. Exactement11 déclarations=9 théorèmes+2 définitions et11 prints qualifiés en ordre, chacun avec seulement propext/Classical.choice/Quot.sound. Zéro print sans axiome, zéro print propext seul, zéro sorryAx/recovery/unsafe/native_decide/axiome supplémentaire, aucune erreur ni avertissement. Exit0 et olean neuf acquittent le module auxiliaire entier. L'ancien FAIL18 n'est ni effacé ni rejoué : ses sept diagnostics techniques, six recovery et zéro crédit restent archivés.

Contenu acquis : expKernel et gammaLine réels, continuité et intégrabilité des deux demi-droitesΓ(2±it), réunion par la mesure préservée sous négation, convergence Mellin de exp(−x), identification du transformé àΓ sur Re(s)>0, intégrabilité verticale Re(s)=2 puis inversion réelle et facteur1/(2π) explicite pour x>0. Le majorant2exp(−πt/4) et sa Laplace intégrable viennent de la dépendance indépendanteΓ02. Aucune intégrabilité ou inversion finale n'est posée en prémisse. Cette identité scalaire réelle ne paie pas l'échange avecΛ, le prolongement à a−iθ, M/H1 uniforme ou une annulation arithmétique finale.

Conservation physiquement rehashée :8456inputs/1214anciens Juge/3089archives/27captures, originaux et copies, gate et Gamma02 intacts. PRE SHA {links["PREEXEC.json"]["sha256"]}, POST SHA {links["POSTEXEC.json"]["sha256"]}, actualreceipt SHA {links["receipt.json"]["sha256"]}. GrandsJSON parsés et tous octets liés recontrôlés, aucune fausse qualification rawFULL de toutes sources d'imports. Tous anciens lots et ce20 clos sans reprise. Baseline79/1328 avant observationROOT ; proposition80/1339 limitée à ce nouveau module11. CoefficientN natif terminé, racines/primalités concrètes, raffinement butterflies/mots/GMP/CRT, correctionPP/frontière, D_N, Goldbach et WIN restent ouverts. BUILD04 est une future revue SOURCE distincte ; aucun build ou lot21 autorisé par cette clôture.
'''
    new(OWN / "adjudication.md", report)
    completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH20", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 1, "declarations_passed": 11, "module_count_passed": 1, "declaration_count_passed": 11,
        "theorems_passed": 9, "definitions_passed": 2, "all_current_bytes_preserved": True, "all_inputs_unchanged": True,
        "input_count": 8456, "closed_judge_file_count": 1214, "protected_archive_count": 3089, "capture_count": 27,
        "print_count": 11, "standard_print_count": 11, "recovery_sorryAx_print_count": 0,
        "declarations_without_axioms": empty, "declarations_with_propext_only": prop,
        "warnings": warnings, "errors": errors, "passed_modules": [MODULE], "failed_modules": [], "not_invoked_modules": [],
        "exact_axiom_rows": parsed, "actual_links": links, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "metadata_close_source_sha256": sha(Path(__file__)), "readonly_local_dependencies": DEPS,
        "recompiled_dependencies": [], "old_batches_recompiled": False, "author_olean_used": False, "retry_count": 0,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "previous_official_modules": 79, "previous_official_declarations": 1328,
        "proposed_new_official_modules": 80, "proposed_new_official_declarations": 1339,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False, "C5_paid": False,
        "global_trace_certified": False, "coefficient_N_computed": False, "concrete_five_root_certificates_paid": False,
        "native_refinement_paid": False, "D_N_paid": False, "WIN": False,
        "full_log_reads": ["aadc49"], "full_actual_receipt_read": "aadc49", "full_START_read": "32c370"}
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 1, "declarations_passed": 11,
        "all_current_bytes_preserved": True, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))


if __name__ == "__main__":
    main()
