"""Fresh batch07 documentary adjudication: hashes/log parsing, no subprocess."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

OWN = Path(__file__).resolve().parent
BASE = OWN.parents[2]
OUT = OWN / "batch07_attempt01"


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


pre, post = load(OUT / "PREEXEC.json"), load(OUT / "POSTEXEC.json")
receipt, catalog = load(OUT / "receipt.json"), load(OWN / "catalog.json")
closed = load(OWN / "closed_judge_bindings.json")
start, finish = load(OUT / "START.json"), load(OUT / "FIN.json")
require(receipt["status"] == "INDEPENDENT_BATCH07_FAILED", "real failed batch")
require(receipt["actual_child_invocations"] == len(receipt["rows"]) == 3, "three real children only")
require(receipt["module_count_passed"] == 2 and receipt["declarations_passed"] == 9, "two PASS nine declarations")
require(not any(receipt[key] for key in ("hidden_retries", "old_batches_recompiled", "numeric_bank_replayed", "author_olean_used")), "no extra invocation")
require(pre["inputs"] == post["inputs"] and pre["protected_archives"] == post["protected_archives"], "identical PRE POST bindings")
require(all(post[key] for key in ("all_inputs_unchanged", "captures_unchanged", "gate_unchanged")), "POST invariance")
for item in pre["inputs"]:
    require(sha(item["path"]) == item["sha256"], "current input " + item["path"])
for item in pre["protected_archives"]:
    require(sha(BASE / item["path"]) == item["sha256"], "current archive " + item["path"])
for item in pre["captures"]:
    require(sha(item["source"]) == sha(item["capture"]) == item["sha256"], "current source and capture bytes")
require(sha(pre["gate_path"]) == pre["gate_sha256"] == start["gate_sha256"], "current gate")
require(len(pre["inputs"]) == 7124 and len(pre["protected_archives"]) == 3089, "input archive counts")
require(len(closed["inputs"]) == 374 and len(pre["captures"]) == 70, "closed capture counts")
input_map = {item["path"]: item["sha256"] for item in pre["inputs"]}
require(all(input_map.get(item["path"]) == item["sha256"] for item in closed["inputs"]), "all closed files verified")
deps = ["GammaPrerequisites22", "GammaDerivative22", "GammaBoxBounds22", "GammaContourComponent22", "GammaPsiCore22", "GammaPsiBetaLimit22", "GammaPsiIntegral22", "ZetaEulerDirect22"]
require(not pre["author_olean_in_lean_path"] and pre["readonly_local_dependencies"] == receipt["readonly_local_dependencies"] == deps, "eight independent readonly dependencies")
cache = BASE.parent / "q356-canonical-binding-replay" / ".lake" / "packages"
expected_path = [str(OUT), str(OWN / "readonly_oleans")] + [str(cache / name / ".lake" / "build" / "lib") for name in ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")]
require(pre["LEAN_PATH"].split(";") == expected_path, "exact independent LEAN_PATH")
require(len(catalog["modules"]) == 8 and catalog["theorem_count"] == 74 and catalog["definition_count"] == 9, "eight modules 83 catalogue entries")
allowed = {"propext", "Classical.choice", "Quot.sound"}
facts = []
for index, module in enumerate(catalog["modules"]):
    name = module["module"]
    require(sha(module["source"]) == module["source_sha256"], "exact frozen source")
    source = Path(module["source"]).read_text(encoding="utf-8")
    require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", source), "no forbidden source token")
    require(len(re.findall(r"^\s*(?:theorem|def)\s+", source, re.M)) == len(module["qualified_prints"]), "all declarations inventoried")
    if index >= 3:
        require(all(not (OUT / (name + suffix)).exists() for suffix in ("_START.json", "_FIN.json", ".log", ".olean")), "downstream NOT_INVOKED")
        facts.append({"module": name, "status": "NOT_INVOKED", "independent_declarations_credited": 0, "source_sha256": module["source_sha256"]})
        continue
    row = receipt["rows"][index]
    require(load(OUT / (name + "_FIN.json")) == row, "FIN exact receipt row")
    mstart = load(OUT / (name + "_START.json"))
    require(mstart["command"] == row["command"] and mstart["module"] == name and mstart["gate_sha256"] == pre["gate_sha256"], "START command provenance")
    require(name == row["module"] and module["source_sha256"] == row["source_sha256"], "order source hash")
    log_path = OUT / (name + ".log")
    require(sha(log_path) == row["log_sha256"], "log immutable bytes")
    log = log_path.read_text(encoding="utf-8")
    prints = [{"declaration": m.group(1), "axioms": [part.strip() for part in m.group(2).split(",") if part.strip()]} for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)]
    require(prints == row["axiom_rows"] and [p["declaration"] for p in prints] == module["qualified_prints"], "exact all qualified prints")
    if index < 2:
        require(row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and row["exit_code"] == 0 and row["exact_axiom_coverage_standard_only"], "real module PASS")
        require(all(set(p["axioms"]) <= allowed for p in prints), "standard axioms only")
        require(not re.search(r"\b(sorryAx|native_decide|Lean\.ofReduceBool)\b|: error:", log), "no recovery error evaluator axiom")
        require(sha(OUT / (name + ".olean")) == row["olean_sha256"], "fresh independent olean")
    else:
        require(row["status"] == "INDEPENDENT_LEAN_AUDIT_FAIL" and row["exit_code"] == 1, "real Gamma reflection FAIL")
        require(row["olean_sha256"] is None and not (OUT / (name + ".olean")).exists(), "no failed olean")
        require(not row["exact_axiom_coverage_standard_only"] and len(prints) == 5, "failed coverage")
        require(all(set(p["axioms"]) <= allowed for p in prints[:3]) and all(set(p["axioms"]) == allowed | {"sorryAx"} for p in prints[3:]), "three diagnostic standard prints and two recovery")
        require(len(re.findall(r": error:", log)) == 3, "three actual diagnostics")
        require("79:2: error: ring failed" in log and "95:69: error: unsolved goals" in log and "98:13: error: unsolved goals" in log, "exact failure locations")
    fact = dict(row)
    fact["independent_declarations_credited"] = len(prints) if index < 2 else 0
    facts.append(fact)

now = datetime.now(timezone.utc).isoformat()
audit = f"""# Adjudication batch07 — auxiliaires — échec partiel

Verdict réel `INDEPENDENT_BATCH07_FAILED` : trois enfants, exactement deux PASS indépendants (Reflection7 + Duplication2 = huit théorèmes/une définition/neuf audits), puis ΓReflection FAIL0 ; cinq modules NOT_INVOKED. Aucun retry/probe/replay/calcul numérique. Gate `{pre['gate_path']}`, SHA `{pre['gate_sha256']}`, lecture FULL6928e5. Unique lanceur dd98c3/session24210 →941895 exit1. START global `{start['time_utc']}`, FIN `{finish['time_utc']}`.

| Module | START UTC | FIN UTC | Exit | Crédit |
|---|---|---|---|---|
| ZetaReflection22 | 13:30:02.218934 | 13:30:25.935890 | 0 | 6 thm +1 def |
| GammaPsiDuplication22 | 13:30:25.952408 | 13:30:39.959350 | 0 | 2 thm |
| GammaPsiReflection22 | 13:30:39.965351 | 13:31:06.269310 | 1 | 0 |

Les neuf audits PASS sont exactement ceux du catalogue et ne dépendent que de `propext`, `Classical.choice`, `Quot.sound`. Aucun `sorry`, `admit`, déclaration `axiom`, `native_decide`, `unsafe` dans les sources PASS ; aucun recovery dans leurs logs. Duplication émet un avertissement de style, sans erreur. Oleans frais : Reflection `{facts[0]['olean_sha256']}`, Duplication `{facts[1]['olean_sha256']}`. Les commands/logs/FIN/reçu lient les sources exactes cc39bd… et 049117… aux nouveaux outputs, sans olean auteur dans LEAN_PATH. Euler n'a pas été recompilé.

Le FAIL ΓReflection est sa première compilation, source8e070c… intacte, log `{facts[2]['log_sha256']}`. Aucun olean. Ses cinq prints sont diagnostics : trois standards, deux derniers `deriv_Gamma_shift_reflection` et `gammaPsi_shift_reflection` avec `sorryAx` de récupération, zéro crédit pour tout le module. Le warning hs0 inutilisé n'est pas une erreur.

Les trois erreurs réelles sont des normalisations non abouties : ligne79, l'égalité h garde les compositions Gamma/sin et `id s` au moment de `linear_combination`, puis ring traite ces applications comme des atomes distincts ; ligne95, `field_simp`/ring laisse Gamma·Gamma⁻¹ malgré les non-annulations établies, avec arguments normalisés s·(±1/2) ; ligne98, le quotient trigonométrique conserve les inverses après normalisation de l'argument du sinus. Les non-annulations de Gamma, sinus, π et s sont présentes dans le contexte. Une éventuelle nouvelle source devra normaliser les applications et quotients avant les tactiques de corps. Le log ne réfute ni l'identité analytique ni un résultat de parité. Aucune modification/reprise du gel actuel.

ChiPsi, Scaled, Envelope, Domination, MixedFubini n'ont aucun START/FIN/log/olean et sont NOT_INVOKED. Leur audit SOURCE antérieur reste distinct d'une preuve compilée. L'ancien Reflection54e32… FAIL batch06 reste archivé : le nouveau PASS cc39bd… ne réécrit pas son journal.

Portée mathématique PASS : Reflection démontre l'équation fonctionnelle de la vraie ζ, la non-annulation de χ et ζ dans −1<Re(s)<0 et le quotient dérivé, en dérivant l'égalité dans un voisinage ouvert et en établissant les dénominateurs. Duplication dérive Legendre pour Re(z)>0 et en déduit ψ(z)+ψ(z+1/2)=2ψ(2z)−2log2 ; tous ses dénominateurs sont prouvés non nuls. Ni trace, intégrabilité finale, non-annulation ζ ou cible D_N ne sont admises comme prémisses libres. Ces conclusions sont auxiliaires. L'identité χ/P1, le noyau, sa domination et le Fubini concret demeurent non compilés ; Mellin, Arch global, orientations, compte complet des zéros, certificats de primitives et coefficient additif N restent ouverts.

Conservation re-vérifiée sur tous les bytes : 7124 inputs, 374 anciens fichiers Juge, 3089 archives, 70 captures exactes source/copie, gate inchangée. PRE/POST bindings identiques. Huit dépendances indépendantes readonly, huit cache libraries ; ni recompilation d'Euler/anciennes dépendances, ni olean auteur. Lean4.15/mathlib9837ca9d fixés. PREEXEC SHA `{sha(OUT / 'PREEXEC.json')}`, POSTEXEC SHA `{sha(OUT / 'POSTEXEC.json')}`, reçu SHA `{sha(OUT / 'receipt.json')}`.

Lectures FULL des logs 39d33f/4beb49/c328c7, reçu7c3b20, START globaux et modules/FIN13dd89. Sources propres ddb5ee/a31e1c/f3e263/dbab7a/90624d/efbf10/c95d0e/63855c ; audit SOURCE407592, catalogue75fc63, reads588ddd. Les gros PRE/POST sont parsés et vérifiés intégralement en metadata avec hashes de tous bytes, sans prétention raw FULL du texte ni des sources mathlib.

Officiel ROOT avant observation : 69 modules/1137 déclarations incluant defs. Ajout potentiel seul : deux modules/neuf déclarations, 71/1146 après ROOT ; les trois prints standards du module FAIL ne sont pas acquis. H1, C5 global, Arch global, D_N et WIN restent ouverts. Créé à {now}, aucune preuve ni ancienne archive modifiée.
"""
write_new(OWN / "adjudication.md", audit)
completion = {"schema": "ROUND22_JUDGE5_DOCUMENTARY_COMPLETION_BATCH07", "time_utc": now,
    "status": receipt["status"], "adjudication_sha256": sha(OWN / "adjudication.md"), "helper_sha256": sha(__file__),
    "actual_receipt_sha256": sha(OUT / "receipt.json"), "PREEXEC_sha256": sha(OUT / "PREEXEC.json"), "POSTEXEC_sha256": sha(OUT / "POSTEXEC.json"),
    "compiler_invocations_in_this_adjudication": 0, "numeric_invocations": 0, "actual_fresh_compiler_invocations_in_batch": 3,
    "modules_passed": 2, "declarations_passed": 9, "theorems_passed": 8, "definitions_passed": 1,
    "modules_failed": 1, "failed_module_declarations_credited": 0, "modules_not_invoked": 5,
    "all_nine_PASS_axiom_prints_exact_standard_only": True, "GammaReflection_errors": 3, "GammaReflection_recovery_prints": 2,
    "inputs_verified": 7124, "closed_judge_verified": 374, "archives_verified": 3089, "captures_verified": 70,
    "all_current_bytes_preserved": True, "large_PRE_POST_raw_FULL_claimed": False,
    "actual_logs_FULL": ["39d33f", "4beb49", "c328c7"], "actual_receipt_FULL": "7c3b20", "START_FIN_FULL": "13dd89",
    "previous_official_modules": 69, "previous_official_declarations": 1137,
    "possible_modules_after_ROOT_observation": 71, "possible_declarations_after_ROOT_observation": 1146, "official_count_requires_ROOT_observation": True,
    "module_facts": facts, "H1_paid": False, "C5_global_paid": False, "D_N_paid": False, "global_trace_certified": False, "WIN": False}
write_new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": receipt["status"], "adjudication_sha256": sha(OWN / "adjudication.md"), "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "compiler_invocations": 0, "numeric_invocations": 0}, ensure_ascii=False))
