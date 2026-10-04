"""Close actual batch08 metadata only. No compiler, import probe or numeric run."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

OWN = Path(__file__).resolve().parent
ACTUAL = OWN / "batch08_attempt01"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(name):
    return json.loads((ACTUAL / name).read_text(encoding="utf-8"))


def main():
    receipt = read("receipt.json")
    pre, post, start, finish = [read(name) for name in
        ("PREEXEC.json", "POSTEXEC.json", "START.json", "FIN.json")]
    catalog = json.loads((OWN / "catalog.json").read_text(encoding="utf-8"))
    assert sha(ACTUAL / "receipt.json") == "64b1138dff5886e7074b6249b62ee0469e39d615b1b302f9d1cb20e0307e9419"
    assert receipt["status"] == "INDEPENDENT_BATCH08_FAILED"
    assert receipt["actual_child_invocations"] == 2 and receipt["declarations_passed"] == 5
    assert receipt["module_count_passed"] == 1 and receipt["all_inputs_unchanged"]
    assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    assert pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 7235 and len(pre["protected_archives"]) == 3089
    assert receipt["closed_judge_file_count"] == 489 and len(pre["captures"]) == 73
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == start["gate_sha256"]
    for item in pre["captures"]:
        assert sha(item["source"]) == item["sha256"] == sha(item["capture"])
    g, chi = receipt["rows"]
    assert g["module"] == "GammaPsiReflection22" and g["exit_code"] == 0
    assert g["status"] == "INDEPENDENT_LEAN_AUX_PASS" and g["exact_axiom_coverage_standard_only"]
    assert [row["declaration"] for row in g["axiom_rows"]] == catalog["modules"][0]["qualified_prints"]
    assert all(set(row["axioms"]) == {"propext", "Classical.choice", "Quot.sound"} for row in g["axiom_rows"])
    assert chi["module"] == "ContourChiPsi22" and chi["exit_code"] == 1
    assert not chi["axiom_rows"] and chi["olean_sha256"] is None
    for row in (g, chi):
        assert sha(ACTUAL / (row["module"] + ".log")) == row["log_sha256"]
        assert read(row["module"] + "_FIN.json") == row
    assert sha(ACTUAL / "GammaPsiReflection22.olean") == g["olean_sha256"]
    assert "must be contained in root directory" in (ACTUAL / "ContourChiPsi22.log").read_text(encoding="utf-8")
    not_invoked = [info["module"] for info in catalog["modules"][2:]]
    for module in not_invoked:
        for suffix in ("_START.json", "_FIN.json", ".log", ".olean"):
            assert not (ACTUAL / (module + suffix)).exists()
    assert not (ACTUAL / "ContourChiPsi22.olean").exists()
    text = f"""# ROLE5 — adjudication réelle partielle batch08

L'unique essai autorisé est clos : 77d367/session51970→3b9adc exit1. START global {start['time_utc']}, FIN global {finish['time_utc']}. Deux véritables enfants ont été lancés, sans retry/probe/numérique. Le résultat est un PASS auxiliaire de cinq théorèmes, un FAIL de configuration avant élaboration, puis quatre NON_INVOQUÉS.

ΓReflection08, source {g['source_sha256']}, a compilé exit0 de {g['started_at']} à {g['finished_at']}. Les cinq noms exacts du catalogue ont chacun [propext, Classical.choice, Quot.sound], sans sorryAx ni axiome ajouté. Log {g['log_sha256']} ; olean indépendant {g['olean_sha256']}. Il prouve la réflexion Gamma et sa dérivée/log-dérivée sur la bande −1<Re(s)<0, avec les non-annulations établies. Il ne prouve ni C5/Fubini ni une trace spectrale globale ou D_N.

Chi09, source {chi['source_sha256']}, a lancé Lean de {chi['started_at']} à {chi['finished_at']}, exit1, zéro print et aucun olean. Son log {chi['log_sha256']} dit que source_final/ContourChiPsi22.lean n'est pas contenu dans la racine batch08/sources, fixée par le cwd du lanceur. Le Juge a manqué cette incompatibilité en préparant une nouvelle copie dans un dossier frère pour conserver la copie préliminaire. Classification : CONFIGURATION_ROOT_PATH_BEFORE_ELABORATION. Aucune déduction analytique, erreur API de preuve, sorryAx de recovery ou obstruction de parité n'est observée. La source Chi09 n'a pas été élaborée et ne reçoit aucun crédit.

NON_INVOQUÉS : {', '.join(not_invoked)} ; aucun START/FIN/log/olean de ces modules. Le lot08 et ses sources/outils restent immuables ; il ne sera pas repris. Un futur lot distinct doit placer les cinq copies restantes sous une racine commune avant son nouveau gel/gate. ΓReflection08 est uniquement une dépendance indépendante readonly de ce futur lot, sans recompilation.

Conservation réelle : PRE/POST identiques pour 7235 inputs et 3089 archives ; 489 anciens fichiers Juge liés, 73 captures/gate intacts, dix dépendances readonly, aucun olean auteur. PRE SHA{sha(ACTUAL / 'PREEXEC.json')}, POST SHA{sha(ACTUAL / 'POSTEXEC.json')}. Logs et reçu réellement lus FULL dabcc4 ; START/FIN globaux et des deux enfants FULL ad78f0. Les grands PRE/POST sont comparés intégralement comme métadonnées et hashes, pas revendiqués raw FULL ni comme lecture mathématique de Mathlib. Reçu réel SHA{sha(ACTUAL / 'receipt.json')}.

Avant observation ROOT, l'officiel reste 71/1146. Le seul incrément éligible est un module/cinq déclarations, soit 72/1151 si ROOT observe la clôture ; aucune définition nouvelle. Aucun budget numérique, H1 complet, C5 archimédien global, coefficient N, D_N ou WIN n'est payé par ce résultat. Le reste de la chaîne demeure ouvert.
"""
    with (OWN / "adjudication.md").open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)
    completion = {"schema": "ROUND22_JUDGE5_BATCH08_COMPLETION", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": "CLOSED_PARTIAL_AUX_PASS5_CONFIG_ROOT_FAIL0_FOUR_NOT_INVOKED", "actual_receipt_sha256": sha(ACTUAL / "receipt.json"),
        "adjudication_sha256": sha(OWN / "adjudication.md"), "compiler_invocations_in_this_closure": 0,
        "numeric_invocations_in_this_closure": 0, "actual_child_invocations": 2, "passed_modules": 1,
        "passed_theorems": 5, "passed_definitions": 0, "failed_modules": 1,
        "failure_classification": "CONFIGURATION_ROOT_PATH_BEFORE_ELABORATION", "not_invoked": not_invoked,
        "axiom_coverage_passed": 5, "standard_only": True, "inputs": 7235, "closed_judge_files": 489,
        "archives": 3089, "captures": 73, "all_inputs_unchanged": True, "old_batches_recompiled": False,
        "prior_official_modules": 71, "prior_official_declarations": 1146,
        "eligible_after_ROOT_observation_modules": 72, "eligible_after_ROOT_observation_declarations": 1151,
        "H1_paid": False, "C5_global_paid": False, "D_N_paid": False, "victory": False}
    with (OWN / "completion_receipt.json").open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(completion, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    print(json.dumps(completion, sort_keys=True))


if __name__ == "__main__":
    main()
