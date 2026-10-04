"""Freeze author FINAL3 from actual receipts; metadata only, no Lean or math."""
import datetime as dt
import json
from pathlib import Path
import sys
import build_once as audit

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
B = W.parents[1]
R = W.parent
gate = B / ".arbor/sessions/parity/.coordinator/messages/round20_formal3_compile_authorization.json"
auth = json.loads(gate.read_text(encoding="utf-8"))
prep = json.loads((W / "preparation.json").read_text(encoding="utf-8"))
ledger = json.loads((W / "build_receipt.json").read_text(encoding="utf-8"))
started = W / "finalize_started.json"
audit.exclusive_json(started, {
    "operation": "freeze_actual_author_receipts_and_report_only",
    "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
    "actual_command": [sys.executable, "-B", str(Path(__file__))],
    "finalizer_sha256": audit.sha(Path(__file__)),
    "ledger_sha256": audit.sha(W / "build_receipt.json"),
    "gate_sha256": audit.sha(gate),
    "additional_lean_invocations": 0, "numeric_invocations": 0
})
with (W / "finalize_source.py.txt").open("xb") as stream:
    stream.write(Path(__file__).read_bytes())
if audit.sha(gate) != "2eed1427b57c873194b37603182e0b5d9a879cb8287c4351cfd638bedca2fa5d":
    raise RuntimeError("root gate binding changed")
if audit.sha(W / "build_once.py") != auth["launcher_sha256"]:
    raise RuntimeError("root-reviewed launcher changed")
if audit.sha(W / "preparation.json") != auth["preparation_sha256"]:
    raise RuntimeError("root-reviewed preparation changed")
audit.verify_bindings(auth["checked_inputs_sha256"], "root-verified canonical numeric bank")
audit.verify_bindings(prep["historical_dependencies_sha256"], "historical imports")
for name, digest in prep["original_documents_sha256"].items():
    if audit.sha(Path(name)) != digest:
        raise RuntimeError(f"original document changed: {name}")

modules = []
for module in audit.MODULES:
    history = [a for a in ledger["attempts"] if a["module"] == module]
    passes = [a for a in history if a["status"] == "PASS_NEW_AUXILIARY_MODULE"]
    if len(passes) != 1 or history[-1] != passes[0]:
        raise RuntimeError(f"exactly one final new PASS required: {module}")
    passed = passes[0]
    if passed["actual_exit_code"] != 0:
        raise RuntimeError("compiler PASS must have actual zero exit")
    for name in ["source_unchanged", "readonly_dependencies_unchanged", "runtime_unchanged",
                 "authorization_unchanged", "canonical_numeric_bank_unchanged"]:
        if passed[name] is not True:
            raise RuntimeError(f"failed postcheck: {module}/{name}")
    for name, digest in [(passed["source_path"], passed["source_sha256"]),
                         (passed["olean_path"], passed["olean_sha256"]),
                         (passed["log_path"], passed["log_sha256"])]:
        if audit.sha(audit.bound_path(name)) != digest:
            raise RuntimeError(f"changed final PASS asset: {name}")
    source_text = audit.bound_path(passed["source_path"]).read_text(encoding="utf-8")
    if audit.FORBIDDEN.search(source_text.split("-- AXIOM_AUDIT_BEGIN")[0]):
        raise RuntimeError("forbidden source proof token")
    log_text = audit.bound_path(passed["log_path"]).read_bytes().decode("utf-8")
    actual_audit = audit.analyze_axioms(log_text, passed["expected_declarations"])
    if not actual_audit["declaration_coverage_exact"] or actual_audit["unexpected_axioms"]:
        raise RuntimeError(f"final axiom audit not exact/allowed: {module}")
    modules.append({"module": module, "passed_attempt": passed["attempt"],
                    "actual_exit_code": 0, "source": passed["source_path"],
                    "source_sha256": passed["source_sha256"], "olean": passed["olean_path"],
                    "olean_sha256": passed["olean_sha256"], "log": passed["log_path"],
                    "log_sha256": passed["log_sha256"],
                    "receipt": f"round20/role3/attempt{passed['attempt']:02d}_{module}_receipt.json",
                    "definitions": passed["written_definitions"], "theorems": passed["written_theorems"],
                    "printed_axioms": len(actual_audit["actual_declarations"]), "axiom_audit": actual_audit})
failures = [a for a in ledger["attempts"] if a["status"] == "FAIL_ACTUAL_NEW_ATTEMPT"]
failure_rows = []
for failure in failures:
    analysis = W / f"attempt{failure['attempt']:02d}_analysis.json"
    if not analysis.is_file():
        raise RuntimeError("every actual failed attempt requires its analysis")
    record = json.loads(analysis.read_text(encoding="utf-8"))
    if record["actual_lean_exit_code"] != failure["actual_exit_code"]:
        raise RuntimeError("failure analysis/compiler exit mismatch")
    failure_rows.append({"attempt": failure["attempt"], "module": failure["module"],
                         "actual_exit_code": failure["actual_exit_code"], "analysis": audit.relative(analysis),
                         "analysis_sha256": audit.sha(analysis), "classification": record["classification"],
                         "log": failure["log_path"], "log_sha256": failure["log_sha256"]})
for attempt in ledger["attempts"]:
    receipt = W / f"attempt{attempt['attempt']:02d}_{attempt['module']}_receipt.json"
    if json.loads(receipt.read_text(encoding="utf-8")) != attempt:
        raise RuntimeError("ledger does not reproduce immutable individual receipt")
    audit.verify_bindings(attempt["readonly_dependencies_sha256"], "attempt readonly imports")
    audit.verify_bindings(attempt["checked_inputs_sha256"], "attempt canonical bank")

numeric = json.loads((R / "composite.json").read_text(encoding="utf-8"))
labels = {
    config: {key: detail[key]["whole_box_certificate"]["sign"]
             for key in ["Gamma0_theta", "Gamma0_raw", "new_principal_minus_M0"]}
    for config, detail in numeric["aggregate_affine_expressions_and_certificates"].items()
}
totals = {"modules": len(modules), "definitions": sum(m["definitions"] for m in modules),
          "theorems": sum(m["theorems"] for m in modules),
          "printed_axioms": sum(m["printed_axioms"] for m in modules)}
module_table = "\n".join(f"| {m['module']} | {m['passed_attempt']} | {m['theorems']} | {m['definitions']} | {m['printed_axioms']} | 0 |"
                         for m in modules)
fail_table = "\n".join(f"| {f['attempt']} | {f['module']} | {f['classification']} | {f['actual_exit_code']} |"
                       for f in failure_rows)
report = f"""# FINAL3 — formalisation composite20, node13.12

Les six nouveaux modules ont chacun un PASS auteur neuf sous Lean4.15.0, sans
`sorryAx` dans leurs 141 audits finaux. Ils démontrent91 théorèmes auxiliaires et
construisent50 définitions. Il y a14 invocations Lean réelles :6 PASS nouveaux et
8 FAIL techniques conservés. Ce résultat est **auxiliaire, sans victoire**. Le
Juge doit encore compiler ses propres copies ; aucun olean auteur20 ne lui donne
un PASS indépendant.

## Résultat compilé et traçabilité

| Module | Tentative PASS | Théorèmes | Définitions | Audits | Exit Lean |
|---|---:|---:|---:|---:|---:|
{module_table}

Chaque tentative possède un START antérieur à Lean, sa commande réelle et son
LEAN_PATH, source/launcher/gate capturés, log brut UTF8, exit, audit et postchecks.
Sources, dépendances, runtime, gate et577 liaisons du banc canonique sont restés
inchangés pendant chaque PASS. Le launcher323fbb9474088a8b09d909815653cfc3137b8c5623c2f5fb94556cbb0433c7d3
et la préparation37c3275b9daff66e8734905be5f6f983ed610ad6f3a51d62e12835a1af87c72e
sont les versions lues et autorisées par root. La préparation est un snapshot
PREEXEC ; les résultats réels sont dans build_receipt.json et les receipts
individuels. Aucune source PASS n'a été rejouée ou modifiée après son PASS.

Les seuls axiomes des déclarations finales sont propext, Classical.choice et
Quot.sound. Certaines définitions n'en utilisent aucun. Les warnings finaux sont
des lint inutilisé/simpa/ring ; aucune erreur Lean ne subsiste dans les logs PASS.

## Portée mathématique précise

1. OddBonferroniArithmetic construit les petits premiers effectifs, leur
   primoriale, ses vrais diviseurs et xi(h)=mu(h) sous omega(h)<=2K+1. La formule
   binomiale utilise le cardinal effectivement rencontré. Le poids vaut1 en
   l'absence de petit facteur et -choose(r-1,2K+1) sinon, donc minore l'indicateur
   roughness. Il ne postule pas un cardinal ou un signe libre.
2. LeastFactorComposite construit minFac(j), son quotient, p²<=j et v>=p. Les
   cellules p non minimal gardent leurs contributions Bonferroni non positives.
   Le cas j=p² et les facteurs répétés sont couverts sans coprimalité(p,v).
3. SwitchedSelbergWeight spécialise les acquis17 au vrai support unitaire
   N*t*p0, avec g(p)=1/phi(p). N pair et z>=1 justifient G>0 et lambda1=1 avant
   toute division. Les coefficients, leur formule Möbius, le poids positif,
   l'expansion double et Q(lambda)=1/G sont construits. Q=1/G seul n'est pas
   une nouvelle estimation uniforme du principal.
4. PhysicalCompositeSubtraction utilise les vrais PhysicalWitness18 et garde
   leur ordre, bulk, unité et front original. Le domaine q est premier, mais
   n'est jamais filtré par Prime(j). L'identité theta=Q-C soustrait tous les
   composites. rawLambda conserve les puissances propres, sans mu(j)^2 ;
   raw=theta+la vraie différence raw-theta est explicite.
5. CompositeAPConductor démontre le conducteur partagé
   nu=p*lcm(h,lcm(k,l)/gcd(lcm(k,l),p)), les équivalences de divisibilité et AP,
   l'incompatibilité réelle des nonunités, le cap entier p²<=j et le kernel
   1/phi(lcm(k,l)). La primoriale p0 vide, la branche p0|t impossible et
   phi(p0*K0)=(p0-1)phi(K0) sont exactes. La compensation Euler totale et une
   amélioration nette de Gamma ne sont pas conclues.
6. SwitchedIncidenceEstimator réindexe les vrais facteurs en catalogue statique
   et développe littéralement Q et Cminus en AP avec les coefficients lambda,
   mu, p² et tous les h/d/e/p. La queue minFac>P et le slack réel restent des
   sommes séparées et non négatives. Le principal est l'intégrale réelle avec
   phi ; chaque reste réel est masse physique moins principal construit.

Sur le frame défini, l'identité finale est

    Ttheta = mainQ - mainC + (actualRQ - actualRC) - Tail - Slack.

La majoration remplace les deux restes par leurs valeurs absolues et garde la
queue soustraite. Les restes ne sont ni postulés petits ni remplacés par une
hypothèse cible. Le corollaire reference_price soustrait un M0 réel arbitraire :
il ne raccorde pas ce symbole au M0 source ni à Gamma0/global D_N.

## Échecs réellement imposés par Lean et corrections

| Tentative FAIL | Module | Nature technique | Exit réel |
|---|---|---|---:|
{fail_table}

Les analyses attempt01/03/05/07/08/10/12/13 décrivent les obligations exactes.
01 : cas if et lambda powerset ;03 : garde opaque et rewrite dans minFac ;
05 : wrappers G/produit vide ;07 : parenthèses du summand raw-theta et branches ;
08 : tactique après goal déjà clos ;10 : wrappers totient et rewrite du quotient ;
12 : contradiction sum_eq_single et types/règles if ;13 : Decidable dépendant
dans un if, résolu par simp de la même équivalence prouvée. Aucune correction
n'ajoute axiome, disponibilité première, petite Gamma ou hypothèse B6/SD.
Ces FAIL ne sont pas des contre-exemples mathématiques et ne prouvent pas que
le mur de la parité a bloqué une déduction.

Incident distinct : après le receipt FAIL01, l'affichage Python cp1252 a rejeté
un caractère Unicode du log. Le log brut et l'exit Lean1 étaient déjà conservés.
Les lancements suivants utilisent PYTHONIOENCODING=utf-8, sans modifier le
launcher gate. La correction de fermeture de section antérieure au premier
EXEC est archivée dans scope_correction20 ; elle ne compte pas comme FAIL Lean.

## Limites et prochain contrôle

Le banc nouveau N=10^8 a un exit canonique0 vérifié par root ; ROLE3 n'a exécuté
aucun producteur numérique. Son statut est
PASS_NEW_COMPOSITE20_FINITE_IDENTITIES_SOURCE_GUARDS_FALSE. Les cinq configurations
ont Gamma0_theta/raw NEG sur toute la boîte acquise de S(N), tandis que
new_principal_minus_M0 est POS. Ces observations finies ont des signes différents
et ne sont pas interchangées. La garde u>=10^24 et la garde x_test<=N/4 sont
fausses au banc. Le seuil source fixé logN>=10^24 est conservé.

Restent ouverts : la bijection complète des frames/AP physiques vers les
fenêtres ordinaires de source et leurs exceptions, B6 analytique avec variation
et constantes, BV/SD au seuil source, la comparaison favorable du principal
total, la compensation et cap p0 à l'échelle source, l'agrégation pondérée par
kappa_c de toutes les incidences et références, capacités/parents, grands
modules et queues, ainsi que le ledger complet D_N. La cible
D_N<=N/(256 logN loglogN) n'est pas démontrée. Aucune victoire n'est déclarée.

Les huit dépendances historiques sont utilisées via leurs olean Judge immuables :
RankCalibrationFace19→SeparatedTypeII18 ; SelbergFourForms17→FourFormRoots17 ;
EulerAnchor16→LeastMissingPrimeMargin16 et ThreeAdicPrimePairing13→ShortDivisorComplement13.
Aucun ancien module, producteur, PASS ou D/W kernel n'est réexécuté.

Fichiers durables : role3/final_manifest.json, role3/final_receipt.json,
role3/build_receipt.json,14 START/log/receipts et huit analyses de FAIL. Sources
et logs PASS listés avec leurs empreintes dans le manifest. Le score reste0.
"""
report_path = R / "agent3_formalisation.md"
with report_path.open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(report)
manifest_path = W / "final_manifest.json"
receipt_path = W / "final_receipt.json"
owned = {audit.relative(path): audit.sha(path) for path in sorted(W.rglob("*"))
         if path.is_file() and path not in [manifest_path, receipt_path]}
owned[audit.relative(report_path)] = audit.sha(report_path)
manifest = {
    "status": "FINAL3_AUTHOR_NEW_AUXILIARY_MODULES_PASSED_NO_WIN", "node_id": "13.12",
    "round": 20, "role": 3, "frozen_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
    "modules": modules, "totals": totals, "actual_lean_invocations": len(ledger["attempts"]),
    "actual_lean_exit_zero": len(modules), "actual_lean_exit_nonzero": len(failures),
    "actual_failed_attempts": failure_rows,
    "allowed_axioms": sorted(audit.ALLOWED_AXIOMS),
    "owned_artifacts_sha256": owned, "report": audit.relative(report_path),
    "report_sha256": audit.sha(report_path), "author_ledger_sha256": audit.sha(W / "build_receipt.json"),
    "compile_gate_sha256": audit.sha(gate), "preparation_sha256": audit.sha(W / "preparation.json"),
    "launcher_sha256": audit.sha(W / "build_once.py"),
    "historical_dependencies_sha256": prep["historical_dependencies_sha256"],
    "canonical_bank_bindings_sha256": auth["checked_inputs_sha256"],
    "stored_numeric_aggregate_labels_only_not_recomputed": labels,
    "stored_source_guards": numeric["source_guards"],
    "original_documents_sha256": prep["original_documents_sha256"],
    "numeric_invocations": 0, "old_rebuilds": 0, "old_PASS_replays": 0,
    "Judge_independent_PASS_not_yet_granted": True, "whole_D_N_bound_proved": False,
    "B6_SD_global_source_price_proved": False, "parity_bypass_proved": False,
    "score": 0, "victory": False
}
audit.exclusive_json(manifest_path, manifest)
receipt = {
    "status": manifest["status"], "node_id": "13.12", "round": 20, "role": 3,
    "finalized_utc": dt.datetime.now(dt.timezone.utc).isoformat(), "totals": totals,
    "actual_lean_invocations": len(ledger["attempts"]), "actual_new_PASS": len(modules),
    "actual_lean_failures": len(failures), "metadata_finalization_additional_lean_invocations": 0,
    "numeric_invocations": 0, "old_rebuilds": 0, "old_PASS_replays": 0,
    "manifest_sha256": audit.sha(manifest_path), "report_sha256": audit.sha(report_path),
    "author_ledger_sha256": audit.sha(W / "build_receipt.json"),
    "finalizer_sha256": audit.sha(Path(__file__)), "finalize_started_sha256": audit.sha(started),
    "compiler_postchecks_and_final_asset_hashes_verified": True,
    "source_freeze_after_six_new_PASS": True, "no_source_or_olean_mutations_by_finalizer": True,
    "score": 0, "whole_D_N_bound_proved": False, "parity_bypass_proved": False, "victory": False
}
audit.exclusive_json(receipt_path, receipt)
print(json.dumps({"receipt": audit.relative(receipt_path), "receipt_sha256": audit.sha(receipt_path),
                  "manifest_sha256": audit.sha(manifest_path), "report_sha256": audit.sha(report_path),
                  "totals": totals, "actual_lean_invocations": len(ledger["attempts"]),
                  "actual_new_PASS": len(modules), "actual_lean_failures": len(failures),
                  "finalizer_lean_invocations": 0, "numeric_invocations": 0, "victory": False}, indent=2))
