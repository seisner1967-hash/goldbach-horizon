"""Close unique actual19 with log metadata and byte hashes only; no compiler."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch19_attempt01"
MODULE = "FiniteFieldProjection22"
GATE_SHA = "d25eeeb3d508341745e05532f6fd5ef511408c2f7be220334cd2ac4b99721c1c"
LOG_SHA = "90fabd8096c829079701138eb43c2acfecf37cea2a30d09a57acf2e5217e078e"
OLEAN_SHA = "0304400125a93cfddace45bcc4428d835c8ee204817f88f156e9fd44ee856f4f"
DEPS = ["QuantizedLambdaEnvelope22", "RationalLogQuantization22"]
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
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH19_AUX_PASS"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == len(receipt["rows"]) == 1
    assert (receipt["modules_passed"], receipt["declarations_passed"]) == (1, 24)
    assert (catalog["module_count"], catalog["total_declarations"], catalog["theorem_count"], catalog["definition_count"]) == (1, 24, 20, 4)
    assert receipt["readonly_local_dependencies"] == DEPS
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert (len(pre["inputs"]), len(old["inputs"]), len(pre["protected_archives"]), len(pre["captures"])) == (8262, 1159, 3089, 29)
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
    assert (len(parsed), len(empty), len(prop), errors, warnings) == (24, 0, 2, 0, 2)
    assert prop == ["GoldbachFiniteFieldProjection22.fieldCharacter", "GoldbachFiniteFieldProjection22.fieldCharacter_nat"]
    assert row["exact_axiom_coverage_standard_only"]
    names = ["START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json",
        MODULE + "_START.json", MODULE + "_FIN.json", MODULE + ".log", MODULE + ".olean"]
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Lot19 clos : PASS indépendant auxiliaire24

Unique exécution2b1567/session63365→411eae exit0, gate FULL54fbd3 SHA {GATE_SHA}, dossier et START absents avant lancement. GlobalSTART {start["time_utc"]}, module {row["started_at"]}→{row["finished_at"]}, globalFIN {fin["time_utc"]}. Un seul enfant FiniteFieldProjection22, aucun timeout/retry/probe/ancien compile/numeric/native build. Commande réelle en START/FIN/reçu ; racine sources unique, deux oleans indépendants PASS17 readonly, aucun olean auteur et aucune recompilation de dépendance. Nouveau olean SHA {OLEAN_SHA} ; source immuable {row["source_sha256"]}.

Log, reçu et globalFIN lus FULL0d4e79, STARTs FULLc1251a. Couverture24 déclarations exactement,20 théorèmes+4 définitions,24 prints en ordre : zéro sans axiomes ; fieldCharacter et fieldCharacter_nat utilisent seulement propext, les22 autres utilisent propext/Classical.choice/Quot.sound. Aucun sorryAx/admit/axiome supplémentaire/unsafe/native_decide ; exit0 et olean neuf indépendants. Deux avertissements linter seulement : hK inutilisé ligne29 et séquence tactique plus générale que nécessaire ligne200 ; aucun diagnostic d'erreur. Le source original reste intégralement conservé.

Portée réelle : orthogonalité géométrique sur corps avec alias signés, garde anti-alias max(N,2M−N)<K, non-annulation de K dans le corps, normalisation inverse, passage du rectangle à l'antidiagonale pour N≤M, DFT à signe−Nj et égalité au coefficient entier A32 canonique. Fact p.Prime et IsPrimitiveRoot ω K sont des hypothèses de domaine explicites qui restent à prouver pour les cinq paramètres concrets. L'expression DFT exacte n'est pas une preuve de butterflies, GMP/mots, catalogue natif, CRT ou calcul du coefficientN. La vraie branche IsPrimePow/minFac inclut toutes puissances premières. Aucune prémisse d'orthogonalité, projection finale, précision ou cible D_N supposée ne paie cette identité.

Conservation physiquement rehashée :8262inputs/1159 anciens Juge/3089archives/29captures, originaux et copies, gate et deux dépendances17 intacts. PRE SHA {links["PREEXEC.json"]["sha256"]}, POST SHA {links["POSTEXEC.json"]["sha256"]}, actualreceipt SHA {links["receipt.json"]["sha256"]}. GrandsJSON parsés et tous octets liés recontrôlés, sans fausse qualification rawFULL de toutes sources d'imports. Tous lots01–18 et ce19 clos sans reprise. Officiel78/1304 reste celui avant l'observation ROOT ; proposition79/1328 uniquement pour ce nouveau module24. H1/globalM/C5, coefficientN natif terminé, correctionPP/frontière, D_N, Goldbach et WIN restent ouverts. Aucun lot20, native build ou nouveau banc autorisé par cette clôture.
'''
    new(OWN / "adjudication.md", report)
    completion = {"schema": "ROUND22_JUDGE5_COMPLETION_BATCH19", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 1, "declarations_passed": 24, "module_count_passed": 1, "declaration_count_passed": 24,
        "theorems_passed": 20, "definitions_passed": 4, "all_current_bytes_preserved": True, "all_inputs_unchanged": True,
        "input_count": 8262, "closed_judge_file_count": 1159, "protected_archive_count": 3089, "capture_count": 29,
        "print_count": 24, "standard_print_count": 24, "recovery_sorryAx_print_count": 0,
        "declarations_without_axioms": empty, "declarations_with_propext_only": prop,
        "warnings": warnings, "errors": errors, "passed_modules": [MODULE], "failed_modules": [], "not_invoked_modules": [],
        "exact_axiom_rows": parsed, "actual_links": links, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "metadata_close_source_sha256": sha(Path(__file__)), "readonly_local_dependencies": DEPS,
        "recompiled_dependencies": [], "old_batches_recompiled": False, "author_olean_used": False, "retry_count": 0,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "previous_official_modules": 78, "previous_official_declarations": 1304,
        "proposed_new_official_modules": 79, "proposed_new_official_declarations": 1328,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False, "C5_paid": False,
        "global_trace_certified": False, "coefficient_N_computed": False, "concrete_five_root_certificates_paid": False,
        "native_refinement_paid": False, "D_N_paid": False, "WIN": False,
        "full_log_reads": ["0d4e79"], "full_actual_receipt_read": "0d4e79", "full_START_read": "c1251a"}
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 1, "declarations_passed": 24,
        "all_current_bytes_preserved": True, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))


if __name__ == "__main__":
    main()
