"""Metadata-only FINAL5 closure after the unique real independent audit.

No subprocess, Lean, audit, producer, kernel, factorization or sign evaluation.
The final receipt cannot bind its own hash; the manifest is bound separately.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import sys

J = Path(__file__).resolve().parent
B = J.parent.parent

def now():
    return datetime.now(timezone.utc).isoformat()

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))

def write_new(path, obj):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(obj, stream, ensure_ascii=False, indent=2, sort_keys=True)
        stream.write("\n")

def freeze_text(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(value)

def numeric_metadata(value):
    if isinstance(value, list):
        return {
            "stored_array_rows": len(value),
            "full_array_preserved_in": "round19/judge/audit_receipt.json",
            "new_numeric_evaluation": False,
        }
    if isinstance(value, dict):
        return {k: numeric_metadata(v) for k, v in value.items()}
    return value

if sys.argv[1:] != ["--after-actual-independent-exit0"]:
    raise SystemExit("Explicit metadata-only FINAL closure argument required")
for name in ("report.md", "audit_summary.json", "closure.json", "manifest.json", "final_receipt.json"):
    if (J / name).exists():
        raise SystemExit(f"No FINAL overwrite or metadata replay: {name}")
source_sha = sha(__file__)
freeze_text(J / "finalize_metadata_source_PREEXEC.py.txt", Path(__file__).read_text(encoding="utf-8"))
started = {
    "phase": "PREEXEC_METADATA_ONLY",
    "started_utc": now(),
    "command": [sys.executable, "-B", "-X", "utf8", str(Path(__file__).resolve()), *sys.argv[1:]],
    "source_sha256": source_sha,
    "source_capture_sha256": sha(J / "finalize_metadata_source_PREEXEC.py.txt"),
    "python_executable": sys.executable,
    "python_sha256": sha(sys.executable),
    "python_version_actual": sys.version,
    "new_Lean_audit_numeric_or_sign_invocations": 0,
}
write_new(J / "finalize_metadata_started.json", started)

audit = read(J / "audit_receipt.json")
launch = read(J / "launch_receipt.json")
prep = read(J / "preparation.json")
assert launch["exit_code"] == 0 and launch["subprocess_launch_error"] is None
assert audit["status"] == "PASS_INDEPENDENT_ROUND19_AUXILIARY_ONLY"
assert not audit["victory"] and not audit["parity_obstacle_bypass_proved"]
assert not audit["full_fixed_D_N_ledger_paid"] and audit["score"] == 0
assert launch["audit_receipt_sha256"] == sha(J / "audit_receipt.json")
assert launch["log_sha256"] == sha(J / "audit.log")
assert launch["preparation_sha256"] == sha(J / "preparation.json")
assert not audit["old_Lean_or_PDF_or_preflight_script_executed"]
assert not audit["producer_kernel_log_or_new_sign_called"]
assert not audit["independent_Lean"]["author19_oleans_used"]
assert not audit["independent_Lean"]["historical_sources_compiled"]
assert audit["preservation_after"]["exact_protected_inventory"] == 1361
assert audit["preservation_after"]["hashes_preserved"]
counts = {"modules": 11, "theorems": 185, "defs": 78, "structures": 3, "instances": 0, "axiom_prints": 268}
assert audit["new_counts"] == counts
modules = audit["independent_Lean"]["modules"]
assert len(modules) == 11
allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
module_rows = []
for m in modules:
    assert m["exit_code"] == 0 and m["status"] == "PASS_FRESH_NEW_INDEPENDENT_LEAN"
    assert read(J / f"{m['module']}_receipt.json") == m
    for path_key, hash_key in (("log", "log_sha256"), ("stdout", "stdout_sha256"), ("stderr", "stderr_sha256"), ("olean", "olean_sha256"), ("source", "source_sha256"), ("source_original", "source_sha256"), ("source_snapshot", "source_sha256")):
        assert sha(m[path_key]) == m[hash_key]
    assert all(set(ax) <= allowed_axioms for ax in m["axioms"].values())
    module_rows.append({key: m[key] for key in (
        "module", "exit_code", "status", "started_utc", "finished_utc", "declaration_counts",
        "axiom_prints", "generated_axiom_prints", "actual_warning_lines", "source_original", "source_sha256",
        "log_sha256", "stdout_sha256", "stderr_sha256", "olean_sha256", "fresh_import_olean_sha256"
    )})

finished_review = now()
summary = {
    "status": "FINAL_FROZEN_INDEPENDENT_AUXILIARIES_PASS_NO_WIN",
    "round": 19, "role": 5,
    "summary_operation": "stored receipts and artifact hashes only; no new mathematical calculation",
    "actual_audit_started_utc": launch["started_at_utc"],
    "actual_audit_finished_utc": launch["finished_at_utc"],
    "actual_audit_exit_code": launch["exit_code"],
    "audit_receipt_sha256": sha(J / "audit_receipt.json"),
    "audit_receipt_bytes": (J / "audit_receipt.json").stat().st_size,
    "audit_log_sha256": sha(J / "audit.log"),
    "launch_receipt_sha256": sha(J / "launch_receipt.json"),
    "authorization_sha256": launch["authorization_sha256"],
    "preparation_sha256": launch["preparation_sha256"],
    "input_manifest_sha256": audit["input_manifest_sha256"],
    "new_counts": counts,
    "previous_official_counts_before_root_closure": audit["previous_counts"],
    "candidate_cumulative_counts_subject_to_root_closure": audit["cumulative_counts"],
    "independent_Lean_actual_invocations": 11,
    "independent_Lean_failures": 0,
    "independent_Lean_PASS_replays": 0,
    "allowed_axioms_only": sorted(allowed_axioms),
    "modules": module_rows,
    "author_invocation_totals": audit["author_invocation_totals"],
    "author_PASS_count": 11,
    "separate_author_Python_SyntaxError_before_any_Lean": 1,
    "stored_numeric_banks": numeric_metadata(audit["stored_numeric"]),
    "nonss_stored_integer_checks": audit["nonss_stored_integer_checks"],
    "rank_stored_integer_checks": audit["rank_stored_integer_checks"],
    "preservation_before": audit["preservation_before"],
    "preservation_after": audit["preservation_after"],
    "source_onset_logN": audit["source_onset_logN"],
    "written_rank3_local_onset_logN": audit["written_rank3_local_onset_logN"],
    "source_onset_applied_to_N_10power8": False,
    "semantic_obligations": audit["semantic_obligations"],
    "compiler_logs_fully_read_after_execution": [m["module"] for m in modules],
    "large_receipt_reading_note": "One raw display was truncated. Selected metadata and all eleven complete compiler logs were read; no claim of a full human display of the fifteen-megabyte certificate index.",
    "new_Lean_audit_numeric_or_sign_invocations_by_finalizer": 0,
    "score": 0, "victory": False, "parity_obstacle_bypass_proved": False,
    "full_fixed_D_N_ledger_paid": False,
    "metadata_review_completed_utc": finished_review,
}
write_new(J / "audit_summary.json", summary)

rows = "\n".join(
    f"| {m['module']} | {m['declaration_counts'].get('theorem', 0)} | {m['declaration_counts'].get('def', 0)} | {m['declaration_counts'].get('structure', 0)} | {m['axiom_prints']} | 0 |"
    for m in modules
)
report = f"""# FINAL5 — Juge Lean indépendant, round19

Verdict : **PASS des identités auxiliaires ; aucune victoire de parité**.
L'unique audit réel a commencé le {launch['started_at_utc']} et s'est terminé
le {launch['finished_at_utc']}, exit0. Les onze compilations neuves ont chacune
réussi au premier passage indépendant. Aucun ancien producteur, kernel,
audit, PDF, sonde de version ou replay PASS n'a été exécuté.

Les nouveaux fichiers contiennent 185 théorèmes explicites, 78 définitions,
trois structures et 268 impressions d'axiomes, dont les deux extensions
générées. Les seuls axiomes observés sont propext, Classical.choice et
Quot.sound. Aucun sorry/admit/native_decide/trustMe/axiom ajouté n'est admis.
Les trois avertissements simpa de UnitLoss aux lignes 25/26/29 sont conservés ; ils ne
sont ni des erreurs ni des justifications pour relancer un PASS.

Le cumul antérieur officiel de 30 modules/507 auxiliaires a été conservé durant
le travail. Le résultat indépendant permet 41 modules/692 auxiliaires après
la clôture du coordinateur. Le présent rôle ne modifie aucun registre global.

| Module neuf | Théorèmes | Définitions | Structures | Prints | Exit |
| --- | ---: | ---: | ---: | ---: | ---: |
{rows}

## Provenance et contrôles effectivement exécutés

L'autorisation canonique ROOT19_JUDGE_CANONICAL_ATTEMPT01 est gelée sous
SHA256 {launch['authorization_sha256']}. La préparation est liée sous
{launch['preparation_sha256']} ; le manifeste PREEXEC est lié sous
{launch['input_manifest_sha256']}. Il conserve 307 entrées FINAL,
26 sources/oleans historiques readonly et 15 captures PREEXEC du lanceur,
de l'audit, de l'autorisation, de la préparation et des onze sources neuves.

Les sources finales des deux auteurs, leurs rapports/reçus, les deux banques
FINAL6 et les revues FINAL1/2 et papier ont été lus avant exécution. Le Juge
compilait seulement les copies fraîches des onze sources du round19. Les imports
Judge18/Judge16/13 et huit bibliothèques du cache mathlib étaient readonly ;
aucun olean auteur du round19 n'a servi. Chaque module possède sa source PREEXEC,
commande, environnement, horodatages, stdout/stderr séparés, log complet,
exit réel et contrôle de tous ses prints. Les onze logs compilateur ont
également été lus intégralement après exécution.

L'inventaire protégé de 1361 entrées et les hashes d'origine sont identiques avant et
après. Audit/lanceur restent respectivement 8aabf796… et f7e22678… : aucune
modification n'a eu lieu après leurs lectures intégrales par le coordinateur.
Le Lean utilisé est le binaire 4.15.0 lié par SHA 8a1ef185… ; la version connue
est metadata historique, sans nouvelle invocation --version.

Les contrôles numériques indépendants utilisent exclusivement les banques
stockées N=10^8. Ils vérifient 1001 positions q, 5120 coordonnées nonSS,
220 images physiques, 48 produits m1 et 47895 paires harmoniques avec diagonale.
Le contrôle de rang décompresse le bitmap stocké sans recrible : 12 millions
d'axes, 719062 bits, 514 fibres, 8868261 axes b et 28136 images physiques beta.
Il vérifie produits/PF fournis, IE complète avec mu0, fronts, P/gcd(P,d),
coefficient maps theta/raw/PP, indices AP et toutes les représentations
stockées. La multiplicité AP combinée stockée est 10 pour chacun des R=2/17.
Aucune primalité, factorisation, valeur W/D/log, fonction S ou signe nouveau
n'est calculé. Les certificats et leurs labels stockés ne sont pas une
expérience supplémentaire. Aucun onset source n'est appliqué à N=10^8.

Le reçu intégral fait 15 341 862 octets parce qu'il conserve les index de
certificats stockés. Une lecture brute affichée a été tronquée ; la synthèse
audit_summary.json lit ses champs stockés et lie son hash, sans prétendre
une lecture humaine intégrale de cet index. Les logs compilateur complets,
les champs structuraux et les obligations sémantiques ont été lus.

## Résultat arithmétique exact et portée

L'extraction terminale utilise les vrais facteurs premiers avec répétitions
et la longueur du multiset. Elle ne suppose pas gcd(h,r)=1. Le premier
manquant canonique, les unités et les fronts dérivent la coprimalité des
ressources à tous rangs. Le tag D/P réserve l'égalité à D. Le conducteur
est inférieur à N ; aucune borne sqrt(N) n'est déduite.

Le CRT est signé dans Z avec constantes, fronts, sélecteur indépendant et
reconstructions réciproques. Le nonSS utilise le sourceBracket importé,
theta/raw et le SS littéral minFac<=Z avec quotient premier. Il conserve
les trois sommes courte/medium/longue et la contribution properpower réelle.
L'injection du produit physique exige M²>N ; m0 raw zéro exige q premier>p0,
et mu(m1)=0 est un zéro littéral. L'identité harmonique porte sur les vrais
cofacteurs de rang 1/2, conserve p² et prouve la converse multiset puis le
raccord Ω(resource)=2/3 vers Ω(cofacteur)=1/2.

Ces équivalences restent sur StructuralSupport/ResourceCell déclaré avec
les deux ressources composites. Elles ne ferment pas le support original
entier : cellules premières/singletons, incidences e1/p0, comparaisons
parents et capacités physiques restent à raccorder au ledger fixé. Aucun
effacement de domaine n'est interprété comme victoire.

La calibration utilise le vrai PhysicalWitness18. La face donne A<=J' et
J'=0 implique A=0. Tous les conducteurs sont conservés avec P/gcd(P,d).
Les prix theta/raw/PP et la référence normalisée complète sont explicites ;
Gamma_rank reste présent. Le prix de perte inclut A*#lost/#U et les fronts+1.
La reconstruction de d*k et le niveau max(aR,R^4) sont arithmétiques.
Le lemme <=32 est celui d'un développement ; il ne paie pas seul les trois
familles AP combinées écrites 40/64. Les sept chi sont les totients exacts.

L'IE garde les diviseurs avec mu0 et le vrai theta_N ; la nullité non unitaire
utilise N-db. Le facteur de face1/phi(P_d) garde ses coprimalités. Les
remainders sont les véritables sommes moins X/phi(dk). L'estimateur exact
et sa borne triangulaire compilent avec X réel explicite ; aucune borne
analytique de ces remainders n'en découle gratuitement. rankMainMass peut
ne pas être positif. Le principal négatif exige M>0 comme garde séparée.

## Lacunes qui empêchent la condition de victoire

La revue papier FINAL19 justifie R1/R2 et la positivité de Md sous les vrais
fronts, y compris les recouvrements de 39 avec N ou d. Elle n'est pas une
attestation Lean de ces nouvelles assertions. La face 1771 exige (P,N)=1
et ne couvre pas tous les N pairs. L'identité Gamma0=Gamma_rank+Pi montre
la compensation exacte : le signe du principal seul ne contrôle pas le
prix physique restant ni l'incidence simultanée de q et N-crsq premiers.

K14 complet, les AP ordinaires non masquées, leurs exceptions N et fronts,
les familles combinées, l'agrégation K18 avec constantes/onset BV et
Gamma_rank restent ouverts. Le nouveau rho/Selberg composite, H7/H9
analytique et les canaux medium/long ne sont pas quantitativement payés.
Le seuil source logN>=10^24 est conservé ; le seuil local écrit 10^40 laisse
10^24..10^40 ouvert. Rangs>=4, T_A, comparaisons parents, capacités uniques
et tous postes du bilan D_N restent ouverts. Le bilan antérieur/A7/C2 est
préservé et aucune prémisse équivalente à la cible n'est introduite.

Aucun des onze modules ne prouve un nouveau contournement quantitatif de
parité applicable au résidu physique complet. D_N<=N/(256 logN loglogN)
n'est pas démontré. Score 0, victoire=false, full_fixed_D_N_ledger_paid=false.

## Échecs réels conservés

Les auteurs ont exécuté 29 invocations Lean : onze premiers PASS et dix-huit
FAIL techniques. Rôle 3 : 17 invocations, 6 PASS/11 FAIL ; rôle 4 : 12 invocations,
5 PASS/7 FAIL. Les sources échouées, leurs captures PREEXEC, logs et exits
restent dans les entrées FINAL. Un SyntaxError du premier lanceur Python
rôle4 avant toute Lean est conservé séparément. Les erreurs de casts,
réécriture dépendante, instances Decidable, récursion de tactiques et
élaboration ne sont pas attribuées au mur de parité. Les sorryAx internes
produits dans les logs d'élaboration échouée ne sont pas des preuves admises.
Le Juge a zéro échec et zéro replay ; toutes les onze compilations sont de
véritables premiers passages indépendants.

Rapport gelé par finalisation metadata seulement. Les reçus réel Lean,
source/log/runtime hashes et manifestes restent la preuve de compilation ;
le verdict sémantique réserve explicitement la victoire.
"""
freeze_text(J / "report.md", report)
(B / "round19" / "agent5.md").write_text(report, encoding="utf-8", newline="\n")
closure = {
    "status": "FINAL5_CLOSED_INDEPENDENT_AUXILIARIES_PASS_NO_WIN",
    "round": 19, "role": 5, "finished_utc": now(),
    "role5_report_sha256": sha(J / "report.md"),
    "agent5_sha256": sha(B / "round19" / "agent5.md"),
    "audit_summary_sha256": sha(J / "audit_summary.json"),
    "audit_receipt_sha256": sha(J / "audit_receipt.json"),
    "launch_receipt_sha256": sha(J / "launch_receipt.json"),
    "canonical_attempts": 1, "independent_Lean_invocations": 11,
    "independent_Lean_PASS": 11, "independent_Lean_FAIL": 0, "PASS_replays": 0,
    "new_counts": counts,
    "prior_official_counts": audit["previous_counts"],
    "candidate_cumulative_counts_for_root_closure": audit["cumulative_counts"],
    "global_registry_or_controller_mutated_by_Judge": False,
    "metadata_finalization_new_Lean_audit_numeric_invocations": 0,
    "source_analytic_obligations": audit["semantic_obligations"],
    "score": 0, "victory": False, "parity_obstacle_bypass_proved": False,
    "full_fixed_D_N_ledger_paid": False,
}
write_new(J / "closure.json", closure)
excluded = {"manifest.json", "final_receipt.json", "finalize_metadata_process.log", "finalize_metadata_process_receipt.json"}
files = [p for p in J.rglob("*") if p.is_file() and p.name not in excluded]
files.append(B / "round19" / "agent5.md")
bindings = {p.relative_to(B).as_posix(): sha(p) for p in sorted(files)}
manifest = {
    "status": "FINAL_FROZEN_JUDGE19_METADATA_MANIFEST",
    "round": 19, "role": 5, "frozen_utc": now(),
    "all_existing_Judge_artifacts_plus_agent5_inventory": True,
    "self_reference_exclusions": sorted(excluded),
    "exclusion_reason": "manifest/final_receipt cannot include their own hashes; actual outer finalizer exit/log are produced after this operation and preserved separately",
    "bindings": bindings,
    "new_Lean_audit_numeric_or_sign_invocations": 0,
}
write_new(J / "manifest.json", manifest)
receipt = {
    "status": "FINAL_FROZEN_INDEPENDENT_AUXILIARIES_PASS_NO_WIN",
    "round": 19, "role": 5, "frozen_utc": now(),
    "manifest_sha256": sha(J / "manifest.json"),
    "closure_sha256": sha(J / "closure.json"),
    "audit_summary_sha256": sha(J / "audit_summary.json"),
    "report_sha256": sha(J / "report.md"),
    "agent5_sha256": sha(B / "round19" / "agent5.md"),
    "audit_receipt_sha256": sha(J / "audit_receipt.json"),
    "actual_audit_exit_code": 0,
    "actual_audit_started_utc": launch["started_at_utc"],
    "actual_audit_finished_utc": launch["finished_at_utc"],
    "new_counts": counts,
    "independent_Lean_invocations": 11, "independent_Lean_PASS": 11,
    "independent_Lean_FAIL": 0, "PASS_replays": 0,
    "all_axioms_standard_only": True,
    "all_declared_FINAL_inputs_read_before_audit": True,
    "all_compiler_logs_fully_read_after_audit": True,
    "protected_inventory": 1361, "protected_hashes_preserved_before_after": True,
    "metadata_finalizer_source_sha256": source_sha,
    "metadata_finalizer_new_Lean_audit_numeric_or_sign_invocations": 0,
    "bindings": bindings,
    "binding_count": len(bindings),
    "binding_keys_relative_to": str(B),
    "actual_outer_metadata_process_exit_and_log": "finalize_metadata_process_receipt.json; preserved separately after this receipt is written",
    "self_reference_exclusions": sorted(excluded),
    "semantic_obligations": audit["semantic_obligations"],
    "score": 0, "victory": False, "parity_obstacle_bypass_proved": False,
    "full_fixed_D_N_ledger_paid": False,
}
write_new(J / "final_receipt.json", receipt)
print(json.dumps({
    "status": receipt["status"], "binding_count": len(bindings),
    "report_sha256": sha(J / "report.md"), "manifest_sha256": sha(J / "manifest.json"),
    "final_receipt_sha256": sha(J / "final_receipt.json"), "closure_sha256": sha(J / "closure.json"),
    "audit_summary_sha256": sha(J / "audit_summary.json"), "new_Lean_audit_numeric_invocations": 0,
}, ensure_ascii=False), flush=True)
