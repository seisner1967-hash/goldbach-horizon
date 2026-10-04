"""New batch06 documentary closure: bytes and logs only, no subprocess."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

OWN = Path(__file__).resolve().parent
BASE = OWN.parents[2]
OUT = OWN / "batch06_attempt01"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def require(condition, label):
    if not condition:
        raise RuntimeError(label)


def write_new(path, text):
    with Path(path).open("x", encoding="utf-8", newline="\n") as handle:
        handle.write(text)


pre = load(OUT / "PREEXEC.json")
post = load(OUT / "POSTEXEC.json")
receipt = load(OUT / "receipt.json")
catalog = load(OWN / "catalog.json")
closed = load(OWN / "closed_judge_bindings.json")
start = load(OUT / "START.json")
finish = load(OUT / "FIN.json")
require(receipt["status"] == "INDEPENDENT_BATCH06_FAILED", "real failed batch")
require(receipt["actual_child_invocations"] == 2, "two real children only")
require(receipt["module_count_passed"] == 1 and receipt["declarations_passed"] == 5, "one module five declarations")
require(not receipt["hidden_retries"] and not receipt["old_batches_recompiled"] and not receipt["numeric_bank_replayed"], "no extra invocation")
require(pre["inputs"] == post["inputs"], "identical input bindings")
require(pre["protected_archives"] == post["protected_archives"], "identical archive bindings")
require(all(post[key] for key in ("all_inputs_unchanged", "captures_unchanged", "gate_unchanged")), "POST invariance")
for item in pre["inputs"]:
    require(sha(item["path"]) == item["sha256"], "current input " + item["path"])
for item in pre["protected_archives"]:
    require(sha(BASE / item["path"]) == item["sha256"], "current archive " + item["path"])
for item in pre["captures"]:
    require(sha(item["source"]) == item["sha256"], "current captured source")
    require(sha(item["capture"]) == item["sha256"], "current immutable capture")
require(sha(pre["gate_path"]) == pre["gate_sha256"] == start["gate_sha256"], "current gate")
require(len(pre["inputs"]) == 7019 and len(pre["protected_archives"]) == 3089, "input/archive counts")
require(len(closed["inputs"]) == 270 and len(pre["captures"]) == 64, "closed/capture counts")
input_map = {item["path"]: item["sha256"] for item in pre["inputs"]}
require(all(input_map.get(item["path"]) == item["sha256"] for item in closed["inputs"]), "all closed files verified")
require(not pre["author_olean_in_lean_path"] and not receipt["author_olean_used"], "independent dependencies")
expected_deps = ["GammaPrerequisites22", "GammaDerivative22", "GammaBoxBounds22", "GammaContourComponent22", "GammaPsiCore22", "GammaPsiBetaLimit22", "GammaPsiIntegral22"]
require(pre["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == expected_deps, "seven readonly dependencies")
cache = BASE.parent / "q356-canonical-binding-replay" / ".lake" / "packages"
expected_path = [str(OUT), str(OWN / "readonly_oleans")] + [str(cache / name / ".lake" / "build" / "lib") for name in ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")]
require(pre["LEAN_PATH"].split(";") == expected_path, "fresh output plus readonly plus eight libraries")
require(len(catalog["modules"]) == 9 and catalog["theorem_count"] == 78 and catalog["definition_count"] == 10, "frozen nine modules 88 declarations")
allowed = {"propext", "Classical.choice", "Quot.sound"}
facts = []
for index, module in enumerate(catalog["modules"]):
    name = module["module"]
    require(sha(module["source"]) == module["source_sha256"], "exact frozen source " + name)
    source = Path(module["source"]).read_text(encoding="utf-8")
    require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", source), "no forbidden source token")
    require(len(re.findall(r"^\s*(?:theorem|def)\s+", source, re.M)) == len(module["qualified_prints"]), "all source declarations counted")
    if index >= 2:
        require(all(not (OUT / (name + suffix)).exists() for suffix in ("_START.json", "_FIN.json", ".log", ".olean")), "downstream not invoked " + name)
        facts.append({"module": name, "status": "NOT_INVOKED", "independent_declarations_credited": 0, "source_sha256": module["source_sha256"]})
        continue
    row = receipt["rows"][index]
    require(load(OUT / (name + "_FIN.json")) == row, "actual FIN equals receipt row")
    require(name == row["module"] and module["source_sha256"] == row["source_sha256"], "order and source")
    log_path = OUT / (name + ".log")
    require(sha(log_path) == row["log_sha256"], "actual log bytes")
    log = log_path.read_text(encoding="utf-8")
    rows = [{"declaration": match.group(1), "axioms": [part.strip() for part in match.group(2).split(",") if part.strip()]} for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)]
    require(rows == row["axiom_rows"], "fresh multiline print parsing")
    require([item["declaration"] for item in rows] == module["qualified_prints"], "complete expected print coverage")
    if index == 0:
        require(row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and row["exit_code"] == 0, "Euler actual PASS")
        require(row["exact_axiom_coverage_standard_only"] and len(rows) == 5, "five Euler audit rows")
        require(all(set(item["axioms"]) <= allowed for item in rows), "Euler standard axioms only")
        require(not re.search(r"\b(sorryAx|native_decide|Lean\.ofReduceBool)\b|: error:", log), "Euler no recovery or error")
        require(sha(OUT / (name + ".olean")) == row["olean_sha256"], "real fresh Euler olean")
    else:
        require(row["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL" and row["exit_code"] == 1, "Reflection actual FAIL")
        require(not row["exact_axiom_coverage_standard_only"] and row["olean_sha256"] is None and not (OUT / (name + ".olean")).exists(), "no failed module olean")
        require(len(rows) == 7 and all(set(item["axioms"]) <= allowed for item in rows[:5]), "five diagnostic standard rows")
        require(all(set(item["axioms"]) == allowed | {"sorryAx"} for item in rows[5:]), "two recovery axioms no credit")
        require(len(re.findall(r": error:", log)) == 10, "ten actual diagnostics")
        require("unknown identifier 'add_neg_eq_sub'" in log and "no goals to be solved" in log and "failed to infer 'have' declaration type" in log, "three technical diagnostic groups")
    fact = dict(row)
    fact["independent_declarations_credited"] = 5 if index == 0 else 0
    facts.append(fact)

now = datetime.now(timezone.utc).isoformat()
audit = f"""# Adjudication indépendante — batch06 — échec partiel

Verdict réel `INDEPENDENT_BATCH06_FAILED`. Deux enfants effectivement invoqués, arrêt au premier FAIL : `ZetaEulerDirect22` PASS indépendant (4 théorèmes, 1 définition), `ZetaReflection22` FAIL (zéro déclaration acquise), sept modules `NOT_INVOKED`. Aucun retry, probe, ancienne compilation ou banc numérique.

## Exécution et portée des audits

Gate ROOT `{pre['gate_path']}`, SHA `{pre['gate_sha256']}`, lecture FULL223645. Unique exécution 3c1fda/session15618 → 2efffa exit1. START global `{start['time_utc']}`, FIN globale `{finish['time_utc']}`.

| Module | START UTC | FIN UTC | Exit | Crédit indépendant |
|---|---|---|---|---|
| ZetaEulerDirect22 | 13:06:18.421201 | 13:06:34.403027 | 0 | 4 théorèmes + 1 définition |
| ZetaReflection22 | 13:06:34.403027 | 13:06:57.853735 | 1 | 0 |

Les cinq déclarations Euler ont chacune un audit exact ne dépendant que de `propext`, `Classical.choice`, `Quot.sound`. Olean frais `{facts[0]['olean_sha256']}`, log `{facts[0]['log_sha256']}`, source `{facts[0]['source_sha256']}`. Aucun token `sorry`, `admit`, déclaration `axiom`, `native_decide`, `unsafe` dans cette source ; aucun recovery dans son log.

Le log Reflection `{facts[1]['log_sha256']}` couvre ses sept prints. Les cinq premiers audits standards ne constituent pas un module compilé. Les deux derniers, `contourChi_differentiableAt` et `contourZeta_logDeriv_reflection`, contiennent `sorryAx` de récupération. Aucun olean produit, aucun crédit. Sa source gelée `{facts[1]['source_sha256']}` demeure intacte, sans token de preuve admise.

Sept non-invoqués : GammaPsiDuplication22, GammaPsiReflection22, ContourChiPsi22, ContourChiScaled22, PsiKernelEnvelope22, PsiKernelDomination22, PsiMixedFubini22. Absence constatée de START/FIN/log/olean pour chacun. Duplication conserve son ancien PASS auteur distinct ; il n'a pas de PASS indépendant dans ce lot. Ces sept modules ne sont pas déclarés FAIL.

## Diagnostic précis

Dix messages techniques se regroupent en trois incidents :

1. Lignes 94–95 : le `have hf` non typé applique `DifferentiableAt.const_cpow` sans fixer le point s. Lean ne synthétise pas x, puis la branche b de `Or.inl`, le placeholder et le type du `have`. Le but de différentiabilité ligne 82 reste ouvert. Une future source distincte doit fixer explicitement le point ou le type ; aucune correction de la source gelée ici.
2. Ligne 124 : `add_neg_eq_sub` est absent du cache fixé. La simplification laisse `(riemannZeta ∘ HSub.hSub 1) s` et le produit par 1 dans hd ; le but exige l'évaluation et la soustraction normalisées. Ce sont des défauts d'API/normalisation.
3. Ligne 131 : une tactique s'exécute après que `field_simp` a déjà fermé le but, `no goals to be solved`.

Le journal ne démontre aucune contradiction de l'identité analytique ni obstruction de parité. Les buts analytiques ne sont pas payés par ces diagnostics ; aucune victoire ne suit du PASS Euler.

## Mathématique effectivement acquise et charges ouvertes

Euler porte sur la vraie `riemannZeta`, sa série dans Re(s)>1 et la sommabilité en norme. Le produit Euler analytique de mathlib, sous ces charges vérifiées dans la preuve, identifie exp de la somme des logarithmes premiers à ζ et entraîne son absence de zéro à droite. Aucune cible D_N, aucune non-annulation ζ libre, aucune hypothèse d'intégrabilité finale ne remplace la conclusion. Les prémisses de domaine et les usages de l'API sont visibles dans la source. Ce module ne donne ni identité de contour globale ni minoration arithmétique.

L'audit SOURCE de Reflection, duplication, χ′/χ, noyau apparié, domination et Fubini reste documentaire pour tout ce qui n'a pas compilé. Le domaine −1<Re(s)<0, les dénominateurs, la continuité, les enveloppes et les vrais passages intégrables ont été examinés en préparation ; aucune de leurs conclusions aval n'est acquise par batch06. Mellin, Arch global, orientations/normalisations finales, queues horizontales, certificat intervalle des primitives, compte exhaustif des zéros, coefficient additif N, D_N restent ouverts.

## Conservation, lectures et compte

7019 inputs, 270 anciens fichiers Juge, 3089 archives et 64 captures source/copie sont re-vérifiés sur tous leurs bytes actuels. Bindings PRE/POST identiques, gate inchangée. Sept dépendances indépendantes readonly, aucune recompilation ; LEAN_PATH contient seulement l'output neuf, leurs copies readonly et huit bibliothèques cache. Aucun olean auteur. Lean4.15/mathlib9837ca9d fixés.

PREEXEC SHA `{sha(OUT / 'PREEXEC.json')}` ; POSTEXEC SHA `{sha(OUT / 'POSTEXEC.json')}` ; reçu effectif SHA `{sha(OUT / 'receipt.json')}`. Logs complets FULL83947d, puis Reflection reread FULL5eee57 ; START/FIN/reçu FULL5dfb6c, puis reçu reread FULLc84866. Sources propres FULL e37773/7f2cb8/ed619f/624c6e/fbcf86/69fda6/d24b1f/844cbd/c7b9c0. Catalogue FULL9c7c55, reads FULLbb5d19, préparation FULL0473df. Les gros PRE/POST ont seulement été lus en projection header/entrée fb1f08, hashés sur tous leurs bytes et vérifiés intégralement par ce helper ; aucune prétention raw FULL de ces JSON ou de toutes les sources mathlib. L'ancienne lecture f3c2c8 tronquée est exclue, remplacée par c7b9c0.

Officiel ROOT avant observation : 68 modules /1132 déclarations auxiliaires incluant définitions. Crédit possible de ce lot : un module/cinq déclarations, soit 69/1137 uniquement après observation ROOT. Aucune extension pour les cinq prints diagnostiques de Reflection. Aucun H1, C3, C5 global, C6 global, trace globale, D_N ou WIN acquis.

Document créé à {now}. Sources, résultats et anciennes archives restent immuables.
"""
write_new(OWN / "adjudication.md", audit)
completion = {
    "schema": "ROUND22_JUDGE5_DOCUMENTARY_COMPLETION_BATCH06",
    "time_utc": now, "status": receipt["status"],
    "adjudication_sha256": sha(OWN / "adjudication.md"), "helper_sha256": sha(__file__),
    "actual_receipt_sha256": sha(OUT / "receipt.json"),
    "PREEXEC_sha256": sha(OUT / "PREEXEC.json"), "POSTEXEC_sha256": sha(OUT / "POSTEXEC.json"),
    "compiler_invocations_in_this_adjudication": 0, "numeric_invocations": 0,
    "actual_fresh_compiler_invocations_in_batch": 2,
    "modules_passed": 1, "declarations_passed": 5, "theorems_passed": 4, "definitions_passed": 1,
    "modules_failed": 1, "modules_not_invoked": 7, "failed_module_declarations_credited": 0,
    "all_five_PASS_axiom_prints_exact_standard_only": True,
    "Reflection_diagnostic_prints": 7, "Reflection_recovery_prints": 2,
    "Reflection_errors": 10, "Reflection_olean_exists": False,
    "inputs_verified": 7019, "closed_judge_verified": 270, "archives_verified": 3089, "captures_verified": 64,
    "all_current_bytes_preserved": True, "large_PRE_POST_raw_FULL_claimed": False,
    "combined_logs_FULL": "83947d", "actual_receipt_and_START_FIN_FULL": "5dfb6c",
    "previous_official_modules": 68, "previous_official_declarations": 1132,
    "possible_modules_after_ROOT_observation": 69, "possible_declarations_after_ROOT_observation": 1137,
    "official_count_requires_ROOT_observation": True,
    "module_facts": facts, "H1_paid": False, "C5_global_paid": False,
    "D_N_paid": False, "global_trace_certified": False, "WIN": False,
}
write_new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": receipt["status"], "adjudication_sha256": sha(OWN / "adjudication.md"), "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
