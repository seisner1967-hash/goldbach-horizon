"""Fresh batch05 documentary adjudication; hashes/parsing only, no subprocess."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

OWN = Path(__file__).resolve().parent
BASE = OWN.parents[2]
OUT = OWN / "batch05_attempt01"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def write_new(path, text):
    with Path(path).open("x", encoding="utf-8", newline="\n") as handle:
        handle.write(text)


def require(condition, label):
    if not condition:
        raise RuntimeError(label)


pre = load(OUT / "PREEXEC.json")
post = load(OUT / "POSTEXEC.json")
receipt = load(OUT / "receipt.json")
catalog = load(OWN / "catalog.json")
closed = load(OWN / "closed_judge_bindings.json")
start = load(OUT / "START.json")
finish = load(OUT / "FIN.json")
require(receipt["status"] == "INDEPENDENT_BATCH05_AUX_PASS", "batch PASS")
require(receipt["actual_child_invocations"] == 2, "exactly two children")
require(pre["inputs"] == post["inputs"], "identical input bindings")
require(pre["protected_archives"] == post["protected_archives"], "identical archive bindings")
require(all(post[key] for key in ("all_inputs_unchanged", "captures_unchanged", "gate_unchanged")), "POST invariance")
for binding in pre["inputs"]:
    require(sha(binding["path"]) == binding["sha256"], "current input " + binding["path"])
for binding in pre["protected_archives"]:
    require(sha(BASE / binding["path"]) == binding["sha256"], "current archive " + binding["path"])
for binding in pre["captures"]:
    require(sha(binding["source"]) == binding["sha256"], "current captured source")
    require(sha(binding["capture"]) == binding["sha256"], "current immutable capture")
require(sha(pre["gate_path"]) == pre["gate_sha256"] == start["gate_sha256"], "current gate")
require(len(pre["inputs"]) == 6707 and len(pre["protected_archives"]) == 3089, "input/archive counts")
require(len(closed["inputs"]) == 209 and len(pre["captures"]) == 32, "closed/capture counts")
input_map = {binding["path"]: binding["sha256"] for binding in pre["inputs"]}
require(all(input_map.get(binding["path"]) == binding["sha256"] for binding in closed["inputs"]), "all closed bindings included and checked")
require(not pre["author_olean_in_lean_path"] and not receipt["author_olean_used"], "independent dependencies")
require(pre["readonly_local_dependencies"] == ["GammaPrerequisites22", "GammaDerivative22"], "readonly dependency names")
cache = BASE.parent / "q356-canonical-binding-replay" / ".lake" / "packages"
expected_path = [str(OUT), str(OWN / "readonly_oleans")] + [str(cache / name / ".lake" / "build" / "lib") for name in ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")]
require(pre["LEAN_PATH"].split(";") == expected_path, "exact fresh output plus readonly plus eight libraries")
allowed = {"propext", "Classical.choice", "Quot.sound"}
module_facts = []
for module, row in zip(catalog["modules"], receipt["rows"], strict=True):
    name = module["module"]
    module_finish = load(OUT / (name + "_FIN.json"))
    require(module_finish == row, "actual FIN equals receipt row")
    require(name == row["module"] and row["exit_code"] == 0, "module order and exit")
    require(row["status"] == "INDEPENDENT_LEAN_AUX_PASS", "module PASS")
    require(row["exact_axiom_coverage_standard_only"], "coverage flag")
    require(sha(module["source"]) == row["source_sha256"] == module["source_sha256"], "exact source")
    require(sha(OUT / (name + ".olean")) == row["olean_sha256"], "real independent olean")
    log_path = OUT / (name + ".log")
    require(sha(log_path) == row["log_sha256"], "actual log")
    log = log_path.read_text(encoding="utf-8")
    rows = []
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S):
        rows.append({"declaration": match.group(1), "axioms": [part.strip() for part in match.group(2).split(",") if part.strip()]})
    require(rows == row["axiom_rows"], "fresh exact multiline print parsing")
    require([item["declaration"] for item in rows] == module["qualified_prints"], "complete catalogue coverage")
    require(all(set(item["axioms"]) <= allowed for item in rows), "standard axioms only")
    require(not re.search(r"\b(sorryAx|native_decide|Lean\.ofReduceBool)\b", log), "no recovery or evaluator axiom")
    source = Path(module["source"]).read_text(encoding="utf-8")
    require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", source), "no forbidden source token")
    require(len(re.findall(r"^\s*(?:theorem|def)\s+", source, re.M)) == len(rows), "all source declarations counted")
    module_facts.append({key: row[key] for key in ("module", "started_at", "finished_at", "exit_code", "source_sha256", "log_sha256", "olean_sha256", "axiom_rows")})
require(sum(len(item["axiom_rows"]) for item in module_facts) == 23, "23 audit rows")
require(catalog["theorem_count"] == 17 and catalog["definition_count"] == 6, "17 theorems and six definitions")
now = datetime.now(timezone.utc).isoformat()
audit = f"""# Adjudication indépendante — batch05 — portée auxiliaire

Verdict réel `INDEPENDENT_BATCH05_AUX_PASS` : exactement deux enfants Lean, sans reprise, 17 théorèmes et six définitions, 23 audits `#print axioms`. Tous les audits ne dépendent que de `propext`, `Classical.choice`, `Quot.sound`. Aucun `sorry`, `admit`, déclaration `axiom`, `native_decide`, `unsafe` dans les deux sources ; aucun `sorryAx` de récupération dans les logs. Deux avertissements de style ΓBox, aucune erreur Lean. Aucun banc numérique exécuté.

## Exécution et provenance

Gate ROOT : `{pre['gate_path']}`, SHA `{pre['gate_sha256']}`, lue FULL a5c206. Une seule invocation du lanceur gelé d7ffee/session91759 → 1cffdc exit0. START `{start['time_utc']}` ; FIN globale `{finish['time_utc']}`. Les deux commandes effectives sont conservées dans les START/FIN de module et le reçu.

| Module | START UTC | FIN UTC | Exit | Déclarations |
|---|---|---|---|---|
| GammaBoxBounds22 | 12:37:05.313458 | 12:37:27.615637 | 0 | 9 théorèmes + 3 définitions |
| GammaContourComponent22 | 12:37:27.615637 | 12:37:50.937286 | 0 | 8 théorèmes + 3 définitions |

ΓBox source `{module_facts[0]['source_sha256']}`, log `{module_facts[0]['log_sha256']}`, olean indépendant `{module_facts[0]['olean_sha256']}`.

ΓContour source corrigée `{module_facts[1]['source_sha256']}`, log `{module_facts[1]['log_sha256']}`, premier olean `{module_facts[1]['olean_sha256']}`. Cette source n'avait pas de compilation auteur acquise. Son premier PASS actuel ne réécrit pas l'ancien échec de la source 244f20 : ancien source/log/FIN capturés et préservés.

Les seuls oleans locaux réutilisés sont ΓPrerequisites22 indépendant batch02 et ΓDerivative22 indépendant batch03, copies exactes readonly. Ils ne sont pas recompilés. LEAN_PATH contient le nouvel output, ce dossier readonly et les huit bibliothèques cache, aucun dossier olean auteur. Lean4.15 et mathlib9837ca9d demeurent fixés.

## Portée mathématique réellement acquise

ΓBox concerne la fonction à valeurs complexes définie par `exp(log(Y)·rho) * Complex.Gamma(rho+1)`, identifiée à `Y^rho Γ(rho+1)` sous Y>0. La borne de dérivée est déduite des bornes Γ et Γ′ indépendamment jugées ; convexité et théorème des accroissements finis donnent la borne Lipschitz sur 0≤Re(rho)≤1, Im(rho)≥gammaLo≥0, Y≥1. Les rayons rectangulaires donnent ensuite l'erreur de transport complète. Les hypothèses d'appartenance à ce domaine sont géométriques ; elles ne certifient ni existence/comptage d'un zéro, ni calcul intervalle d'une valeur Γ au centre. La formule de rayon est continue pour Y>0 ; sa validité comme majorant conserve Y≥1.

ΓContour concerne le même facteur le long de c+i·epsilon·t, c∈[−1/2,3/2], |epsilon|=1. La continuité réelle utilise la différentiabilité de Γ dans le demi-plan droit, avec la composition corrigée explicite. La borne Γ sur Re(rho+1)∈[1/2,5/2] et la monotonie de Y^Re(rho) donnent (27/5)·Y^(3/2)·exp(−πt/4) sous Y≥1,t≥0. L'intégrabilité exponentielle provient de la vraie intégrale Laplace déjà payée ; le changement d'échelle et l'intégrale impropre démontrée dans mathlib donnent sa primitive exacte. Mesurabilité via continuité, domination `mono'` et monotonie de l'intégrale établissent réellement l'intégrabilité L1 et la queue fermée

`(27/5) · Y^(3/2) · exp(−πT/4) / (π/4)` pour T≥0.

Ni l'intégrabilité finale ni le majorant final ne sont des prémisses libres. Les hypothèses libres de ce théorème sont les domaines Y≥1, c∈[−1/2,3/2], |epsilon|=1, T≥0. L'enveloppe définie est continue sur tout ℝ×ℝ ; sa positivité exige Y≥0 et son usage comme borne conserve le domaine précédent. Le module ne porte pas sur le produit avec ζ′/ζ, les côtés horizontaux, les résidus, le compte complet des zéros ou l'intégrale archimédienne globale.

## Conservation et lectures

PREEXEC SHA `{sha(OUT / 'PREEXEC.json')}` ; POSTEXEC SHA `{sha(OUT / 'POSTEXEC.json')}`. Les 6707 inputs, 209 anciens fichiers Juge, 3089 archives et 32 captures ont été re-vérifiés sur leurs bytes actuels par la seule adjudication metadata. PRE/POST ont des bindings identiques, gate et captures conservées. Aucune ancienne compilation, aucune ancienne banque rejouée.

Sources propres FULL 9ca5d5/2e798b ; START/FIN/reçu FULL dd3834 ; vrais logs combinés stdout+stderr FULL ac5b92. PRE/POST : projections de headers 44d80f, hashes de tous bytes daa982, validation intégrale des bindings par ce helper ; aucune prétention raw FULL des gros JSON. Catalogue FULL59c79b et reads FULL10f5d7 avaient déjà clos la préparation. La lecture d4b140 a cherché un nom de log inexistant ; l'inventaire c35f98 et la lecture ac5b92 corrigent cet incident de lecture metadata, sans compilation supplémentaire.

Officiel ROOT avant observation : 66 modules /1109 déclarations auxiliaires avec définitions. Ce lot ajoute deux modules/23 déclarations ; 68/1132 demeure soumis à observation ROOT. Aucun crédit H1, C3, C5, C6, trace globale, coefficient N, D_N ou WIN. Le travail analytique et numérique global reste ouvert.

Adjudication créée à {now}. Reçu effectif SHA `{sha(OUT / 'receipt.json')}`. Toutes les sources et tous les résultats effectifs restent immuables.
"""
audit_path = OWN / "adjudication.md"
write_new(audit_path, audit)
completion = {
    "schema": "ROUND22_JUDGE5_DOCUMENTARY_COMPLETION_BATCH05",
    "time_utc": now,
    "status": receipt["status"],
    "adjudication_sha256": sha(audit_path),
    "helper_sha256": sha(__file__),
    "actual_receipt_sha256": sha(OUT / "receipt.json"),
    "PREEXEC_sha256": sha(OUT / "PREEXEC.json"),
    "POSTEXEC_sha256": sha(OUT / "POSTEXEC.json"),
    "compiler_invocations_in_this_adjudication": 0,
    "numeric_invocations": 0,
    "actual_fresh_compiler_invocations_in_batch": 2,
    "declarations": 23, "theorems": 17, "definitions": 6,
    "inputs_verified": 6707, "closed_judge_verified": 209,
    "archives_verified": 3089, "captures_verified": 32,
    "all_current_bytes_preserved": True,
    "all_23_axiom_prints_exact_standard_only": True,
    "combined_logs_FULL": "ac5b92", "actual_receipt_and_START_FIN_FULL": "dd3834",
    "sources_FULL": ["9ca5d5", "2e798b"],
    "large_PRE_POST_raw_FULL_claimed": False,
    "previous_official_modules": 66, "previous_official_declarations": 1109,
    "possible_modules_after_ROOT_observation": 68,
    "possible_declarations_after_ROOT_observation": 1132,
    "official_count_requires_ROOT_observation": True,
    "module_facts": module_facts,
    "H1_paid": False, "C3_paid": False, "C5_paid": False, "C6_paid": False,
    "D_N_paid": False, "global_trace_certified": False, "WIN": False,
}
completion_path = OWN / "completion_receipt.json"
write_new(completion_path, json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"adjudication_sha256": sha(audit_path), "completion_receipt_sha256": sha(completion_path), "status": receipt["status"], "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
