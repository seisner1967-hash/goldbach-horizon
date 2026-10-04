"""Close a finished Judge20 audit using byte/receipt metadata only."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def exclusive(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")


def main():
    result = load(HERE / "audit_receipt.json")
    launch = load(HERE / "launch_receipt.json")
    post = load(HERE / "launch_post_integrity.json")
    assert result["status"] == "PASS_INDEPENDENT_ROUND20_AUXILIARY_ONLY"
    assert launch["actual_exit_code"] == 0 and launch["launch_error"] is None
    assert post["credited_pass"] is True and post["all_frozen_bindings_unchanged"] is True
    assert result["victory"] is False and result["score"] == 0
    assert result["new_counts"]["modules"] == 16
    started = load(HERE / "audit_started.json")
    inputs = load(HERE / "input_manifest.json")
    checked = {}
    for group in ("final_input_sha256", "historical_dependencies_sha256", "numeric_frozen_sha256",
                  "new_module_sources_sha256", "previous_artifacts_sha256",
                  "original_documents_sha256", "runtime_bindings_sha256"):
        for name, digest in inputs[group].items():
            path = Path(name) if Path(name).is_absolute() else BASE / name
            assert sha(path) == digest
            checked[str(path.resolve())] = digest
    for name, digest in inputs["judge_code_sha256"].items():
        assert sha(HERE / name) == digest
    assert sha(HERE / "preparation.json") == inputs["preparation_sha256"]
    assert sha(HERE / "authorization.json") == inputs["authorization_sha256"]
    assert sha(HERE / "audit.log") == launch["audit_log_sha256"]
    assert sha(HERE / "audit_receipt.json") == launch["audit_receipt_sha256"]
    rows, warnings = [], []
    for row in result["independent_Lean"]["modules"]:
        name, spec = row["module"], row["declaration_specification"]
        assert row["actual_exit_code"] == 0 and row["status"] == "PASS_FRESH_INDEPENDENT_LEAN"
        assert sha(row["source"]) == sha(row["source_original"]) == row["source_sha256"]
        assert sha(HERE / "audit" / (name + ".olean")) == row["olean_sha256"]
        for value in row["outputs"].values():
            assert sha(value["path"]) == value["sha256"]
        assert set(row["axioms"]) == set(spec["requested_axiom_prints"])
        assert all(set(values) <= {"propext", "Classical.choice", "Quot.sound"} for values in row["axioms"].values())
        counts = spec["declaration_counts"]
        rows.append(f"| {name} | {counts.get('theorem', 0)} | {counts.get('def', 0)} | {counts.get('structure', 0)} | {row['axiom_prints']} | 0 |")
        warnings.extend({"module": name, "warning": line} for line in row["warning_lines"])
    totals, authors = result["new_counts"], result["author_attempts"]["totals"]
    report = f"""# FINAL5 — Juge indépendant20 : PASS auxiliaire, victoire non atteinte

Les seize copies fraîches ont réellement compilé sous Lean4.15.0, exit0,
avec {totals['theorems']} théorèmes, {totals['defs']} définitions, {totals['structures']} structure et
{totals['axiom_prints']} impressions d'axiomes couvrant exactement toutes les déclarations
explicites. Aucun `sorryAx`, `sorry`, `admit`, axiome ajouté, `native_decide`,
`trustMe` ou déclaration unsafe n'est accepté. Les seuls axiomes imprimés sont
`propext`, `Classical.choice`, `Quot.sound`, ou aucun axiome.

Il s'agit d'un PASS indépendant **auxiliaire**. La borne globale
`D_N <= N/(256*log N*loglog N)` et le contournement de parité restent non prouvés.
Score0 ; WIN=false. Le cumul d'ingrédients indépendamment audités est désormais
{result['cumulative_counts']['modules']} modules/{result['cumulative_counts']['theorems']} théorèmes, sous réserve de
l'enregistrement du coordinateur ; ce compte ne mesure pas une preuve Goldbach.

## Compilations effectivement observées

| Module neuf | Théorèmes | Définitions | Structures | Audits axiomes | Exit |
|---|---:|---:|---:|---:|---:|
{chr(10).join(rows)}

Le START unique du Juge est {started['started_utc']} ; la fin du child est
{launch['finished_utc']}. Il n'y a qu'une invocation du lanceur et seize
invocations Lean nouvelles, zéro FAIL du Juge et zéro ancien module recompilé.
Les anciennes dépendances13/16/17/18/19 sont importées en lecture seule.
`LEAN_PATH` contient exclusivement `judge/audit`, les répertoires historiques
gelés et les huit bibliothèques cache. Il exclut tous les oleans auteurs20.
Chaque nouvelle dépendance est satisfaite par son propre PASS frais antérieur.

La gate root a le SHA {inputs['authorization_sha256']}, la préparation finale
{inputs['preparation_sha256']}, le manifeste PREEXEC
{sha(HERE / 'input_manifest.json')}. Sources originales/captures/copies,
lanceurs/gate/préparation, runtimes, logs stdout/stderr, codes réels et oleans
sont conservés. Avant/après chaque module et à la clôture, tous les bindings
gelés sont inchangés ; {len(checked)} chemins distincts ont encore été vérifiés
par cette clôture metadata. Aucun producteur, noyau D/W, logarithme, signe,
factorisation, test premier, banque, ancien PASS ou PDF n'a été réexécuté.

## Ce que les preuves démontrent

La piste13.12 construit le Bonferroni impair sur la vraie primoriale et ses
diviseurs. Les composites sont partitionnés par minFac avec p² et p|v permis ;
les cellules non minimales gardent leurs contributions non positives.
Le domaine q provient des vrais PhysicalWitness18 et n'est pas filtré par
Prime(j). Le poids Selberg est construit, lambda1=1 et Q=1/G sont établis.
La soustraction theta enlève tous les composites ; le raw vonMangoldt reste
distinct et conserve ses puissances propres, sans masque mu(j)².

Le conducteur est le vrai p*lcm(h,lcm(k,l)/gcd(lcm(k,l),p)), avec incompatibilités
et caps entiers. L'expansion AP conserve toutes les représentations signées.
L'identité finale est `Ttheta=mainQ-mainC+(actualRQ-actualRC)-Tail-Slack`.
Les deux remainders sont effectivement masse physique moins principal construit.
Leur majoration par ABS n'est pas une estimation de distribution source.
Le corollaire reference_price a un M0 réel **arbitraire** ; il ne prouve pas
son raccord au M0 littéral acquis. B6, SD, BV/onsets, principal favorable,
agrégation pondérée et bridge des frames restent ouverts.

La piste14.5 démontre une borne source réelle au seul seuil `log N>=10^24` :
`sourceFriableAbsoluteCost N <= N/(8192*log N*loglog N)`.
Ce coût est la demande theta en ABS sur H19 filtré F0 ou F1, plus la réciproque
F1 physique unique en ABS, après fusion des e en image q. TK, les vrais tails
Euler et les gardes de floors/ceils sont dérivés ; aucune petite masse libre
ou bonne disponibilité n'est prise en prémisse. Tous les +1 et tous les rangs
de ce domaine sont présents. Les enveloppes raw sont locales ; le budget
source agrégé retenu est theta, sans second paiement de Bpp.

Les m1 non friables de F0 privé de F1 restent hors du coût réciproque payé.
Le complément non friable, H19 vers support source entier, la réunion de tous
les vertices et capacités, singletons/e1/p0/faces/nonbulk, medium/long,
Gamma/T_A/parents/W et le ledger complet restent distincts et ouverts.
Le Juge ne déduit aucune partition croisée entre les deux nouvelles pistes.

## Échecs conservés et portée numérique

Les auteurs ont {authors['actual_invocations']} invocations Lean réelles :
{authors['actual_PASS']} PASS nouveaux et {authors['actual_FAIL']} FAIL techniques. Tous les logs exacts,
START, snapshots et exits restent liés au manifeste gelé. Les `sorryAx`
propagés dans les FAIL ne reçoivent aucun crédit. Les corrections portent sur
binders, wrappers, coercions, API, algèbre et tactiques, sans nouvelle prémisse
analytique. Aucun FAIL n'est inventé comme preuve d'obstacle de parité.
L'incident cp1252 d'affichage est distinct de l'exit Lean déjà conservé.

Le Juge lit seulement les résultats et reçus des deux banques20 canoniques
exit0, avec gardes source FALSE à N=10^8. Il ne recalcule pas leurs signes.
Les labels stockés distinguent les Gamma theta/raw NEG et les nouveaux
principaux moins M0 POS dans les cinq configurations composites ; ceci ne
transporte aucun signe au régime source. Le banc friable observe ses quinze
réciproques F1 uniques et quatre F0 privé de F1 impayées, sans certifier le
budget analytique. Ces observations finies ne donnent pas le target D_N.

La préparation initiale v01 contenait une lecture de N au mauvais niveau JSON.
Ce schéma a été corrigé avant toute gate/START Juge ; source/préparation01 sont
archivées NOT_EXECUTED. Cette révision statique n'est aucun FAIL Lean ou numérique.

## Artefacts et compétences

`judge/audit_receipt.json` est le reçu machine complet ; `launch_receipt.json`
conserve l'exit réel et le hash du log ; `launch_post_integrity.json` accorde
le crédit seulement avec intégrité inchangée. Chaque module possède son
START, invocation brute, stdout/stderr/log, postcheck et reçu audité.
Le rapport mathématique du Juge s'appuie sur les FINAL1/2/3/4/6 et géométrie
lus intégralement, les sources finales Budget/Estimator/Subtraction/Conductor
lues intégralement, ainsi que les définitions/déclarations des seize sources
scannées et contrôlées par Lean. Il ne prétend pas avoir affiché FULL les
565KB de dictionnaires opaques de hashes ni les deux grands résultats JSON.

Les fichiers sont désormais gelés. Aucun PASS ni échec inchangé ne doit être
rejoué. Le coordinateur conserve les acquis, enregistre score0 et retourne à
l'idéation avec les obligations source effectivement manquantes.
"""
    report_path = ROUND / "agent5_judge.md"
    with report_path.open("x", encoding="utf-8", newline="\n") as f:
        f.write(report)
    adjudication = {"status": "PASS_INDEPENDENT_ROUND20_AUXILIARY_ONLY", "round": 20, "role": 5,
        "new_counts": totals, "cumulative_counts": result["cumulative_counts"],
        "actual_unique_judge_launcher_invocations": 1, "actual_new_Lean_invocations": 16,
        "actual_judge_FAIL": 0, "actual_author_totals": authors, "numeric_math_replays": 0,
        "author20_oleans_imported": False, "frozen_inputs_unchanged": True,
        "report": str(report_path), "report_sha256": sha(report_path),
        "audit_receipt_sha256": sha(HERE / "audit_receipt.json"),
        "launch_receipt_sha256": sha(HERE / "launch_receipt.json"),
        "warnings": warnings, "semantic_obligations": result["semantic_obligations"],
        "source_friable_cost_bound_proved": True, "whole_D_N_target_proved": False,
        "parity_bypass_proved": False, "full_fixed_D_N_ledger_paid": False, "score": 0, "victory": False}
    exclusive(ROUND / "adjudication.json", adjudication)
    final_files = {}
    for path in HERE.rglob("*"):
        if path.is_file() and path.name not in {"final_manifest.json", "final_receipt.json"}:
            final_files[path.relative_to(BASE).as_posix()] = sha(path)
    for path in (report_path, ROUND / "adjudication.json"):
        final_files[path.relative_to(BASE).as_posix()] = sha(path)
    exclusive(HERE / "final_manifest.json", {"status": "FINAL_JUDGE20_FROZEN_METADATA_ONLY",
        "created_utc": datetime.now(timezone.utc).isoformat(), "bindings": final_files,
        "binding_count": len(final_files), "checked_input_path_count": len(checked), "victory": False})
    receipt = {"status": "FINAL5_ACTUAL_INDEPENDENT_LEAN_AUXILIARY_NO_WIN", "round": 20, "role": 5,
        "finished_utc": datetime.now(timezone.utc).isoformat(), "new_counts": totals,
        "cumulative_counts": result["cumulative_counts"], "actual_judge_Lean_invocations": 16,
        "actual_judge_FAIL": 0, "actual_author_totals": authors, "all_axioms_standard": True,
        "source_and_outputs_frozen": True, "new_math_during_finalization": False,
        "checked_input_path_count": len(checked), "manifest_binding_count": len(final_files),
        "report_sha256": sha(report_path), "adjudication_sha256": sha(ROUND / "adjudication.json"),
        "final_manifest_sha256": sha(HERE / "final_manifest.json"),
        "audit_receipt_sha256": sha(HERE / "audit_receipt.json"),
        "launch_receipt_sha256": sha(HERE / "launch_receipt.json"), "score": 0, "victory": False}
    exclusive(HERE / "final_receipt.json", receipt)
    print(json.dumps(receipt, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
