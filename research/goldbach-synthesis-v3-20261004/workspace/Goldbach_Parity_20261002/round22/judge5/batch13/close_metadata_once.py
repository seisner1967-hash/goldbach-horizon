"""Close the actual independent PASS once using physical hashes and log metadata only."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch13_attempt01"

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))

def new(path, text):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)

def main():
    assert not (OWN / "adjudication.md").exists()
    assert not (OWN / "completion_receipt.json").exists()
    receipt = read(ACTUAL / "receipt.json")
    pre = read(ACTUAL / "PREEXEC.json")
    post = read(ACTUAL / "POSTEXEC.json")
    start = read(ACTUAL / "START.json")
    fin = read(ACTUAL / "FIN.json")
    catalog = read(OWN / "catalog.json")
    old = read(OWN / "closed_judge_bindings.json")
    manifest = read(OWN / "prepared_manifest.json")
    assert len(receipt["rows"]) == len(catalog["modules"]) == 1
    row = receipt["rows"][0]
    assert receipt["status"] == fin["status"] == "INDEPENDENT_BATCH13_AUX_PASS"
    assert receipt["actual_child_invocations"] == fin["actual_child_invocations"] == 1
    assert receipt["modules_passed"] == 1 and receipt["declarations_passed"] == 20
    assert row["module"] == "ThermalProjectionIdentity22" and row["exit_code"] == 0
    assert row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and row["exact_axiom_coverage_standard_only"]
    assert not row["timed_out"] and row["launch_error"] is None
    assert row["olean_sha256"] == "eb0d3ff46b36861830c6f1656bba68262690054d1ef8739ecbb7b95d5da8ac86"
    assert sha(ACTUAL / "ThermalProjectionIdentity22.olean") == row["olean_sha256"]
    assert row["log_sha256"] == "1fac91b5dedd0c9c251da1d563c20aea51eff7d447453a656313dc7533814490"
    assert sha(ACTUAL / "ThermalProjectionIdentity22.log") == row["log_sha256"]
    assert row["source_sha256"] == "8bb1eb5ec6ab4bf5e0c8cc053dcbe743049641dab5a3a3858205ad8ee2e2e9aa"
    assert sha(OWN / "sources" / "ThermalProjectionIdentity22.lean") == row["source_sha256"]
    assert read(ACTUAL / "ThermalProjectionIdentity22_FIN.json") == row
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 7997 and len(old["inputs"]) == 861
    assert len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 25
    for item in pre["inputs"] + old["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == sha(item["capture"]) == item["sha256"]
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"] == start["gate_sha256"]
    assert pre["gate_sha256"] == "51a5c3577af773a921bda003ac1e0c67ed6ab01e804382d3803e5aba4c531a19"
    assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    assert receipt["all_inputs_unchanged"] and receipt["all_current_bytes_preserved"]
    assert not any(receipt[name] for name in ("author_olean_used", "hidden_retries", "numeric_bank_replayed", "old_batches_recompiled"))
    log = (ACTUAL / "ThermalProjectionIdentity22.log").read_text(encoding="utf-8")
    raw = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)
    audits = [{"declaration": name, "axioms": [value.strip() for value in (values or "").replace("\n", " ").split(",") if value.strip()]} for name, values in raw]
    assert audits == row["axiom_rows"]
    assert [item["declaration"] for item in audits] == catalog["modules"][0]["qualified_prints"]
    standard = {"propext", "Classical.choice", "Quot.sound"}
    assert len(audits) == 20 and all(set(item["axioms"]) == standard for item in audits)
    empty = [item["declaration"] for item in audits if not item["axioms"]]
    assert not empty and "sorryAx" not in log
    assert not re.findall(r":\d+:\d+: error:", log)
    assert len(re.findall(r":\d+:\d+: warning:", log)) == 3
    source = (OWN / "sources" / "ThermalProjectionIdentity22.lean").read_text(encoding="utf-8")
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", source)
    assert len(re.findall(r"^theorem\s+", source, re.M)) == 18
    assert len(re.findall(r"^(?:noncomputable\s+)?def\s+", source, re.M)) == 2
    names = ("START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json",
             "ThermalProjectionIdentity22_START.json", "ThermalProjectionIdentity22_FIN.json",
             "ThermalProjectionIdentity22.log", "ThermalProjectionIdentity22.olean")
    links = {name: {"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in names}
    report = f'''# Juge indépendant — lot13 clos, AUX_PASS20

Une seule exécution réelle : edd769/session89002→2eb8e5, exit0. Gate {pre["gate_sha256"]}, lue FULL0524e3. Global START {start["time_utc"]}, FIN {fin["time_utc"]}. Identity03 START {row["started_at"]}, FIN {row["finished_at"]}, exit0 ; nouvel olean {row["olean_sha256"]}. Status exact {receipt["status"]}. Un module et20déclarations auxiliaires créditables après observation ROOT :18théorèmes,2définitions.

Source03 {row["source_sha256"]} immuable, copie indépendante et root sources commun. Lean4.15.0/cache mathlib9837ca9d existants. Envelope42 PASS11 source77cdab8bed77a3580767bf20dfa8069860ea888490d673daf5144f1aba050ed5/olean9c2bb947ccd03436c8cb3c9e3e9f5ce95508ee719e506d9ca90c49623f6dac67 est la seule dépendance locale readonly ; elle n'a pas été recompilée. Aucun olean auteur, retry, probe, ancien module ou calcul numérique.

Log FULL e42839, SHA {row["log_sha256"]}. Reçu/START/FIN FULL b3372a ; reçus module START/FIN FULL d63e6f. Vingt audits exactement dans l'ordre du catalogue, chacun dépend uniquement de propext, Classical.choice et Quot.sound. Aucune déclaration sans axiomes, aucun sorryAx, aucune erreur, trois warnings unnecessarySeqFocus seulement. Les noms et listes exacts sont conservés dans le log et le reçu. La SOURCE n'a aucun sorry/admit/axiom/native_decide/unsafe. Cette nouvelle invocation clôt le raccord de casts observé FAIL12 ; aucun ancien lot n'a été repris.

Portée mathématique : sous a>0, la projection intégrale continue normalisée exp(aN)/(2π) de T_a(θ)conj(T_a(−θ))exp(−iNθ) égale exactement la somme de m=0 à N de Λ(m)Λ(N−m), avec les vrais poids de von Mangoldt et leurs puissances premières. L'orthogonalité entière, les intégrales finies avec volume, la normalisation et l'antidiagonale sont prouvées. Envelope42 construit les bornes A=r/(1−r)^2 et B=r^(M+1)((M+1)/(1−r)+A), r=exp(−a), la continuité et l'intégrabilité. Identity20 paie B→0, la convergence uniforme, l'erreur d'intégrale→0 et le passage des troncatures M≥N à la trace complète, sans hypothèse finale d'intégrabilité, d'égalité ou de cible. Les identités finies autorisent a réel ; le passage infini utilise réellement a>0.

Conservation physiquement revérifiée par close_metadata_once.py :7997inputs,861anciensJuge,3089archives,25captures, gate, source et dépendance readonly inchangés. PRE SHA {links["PREEXEC.json"]["sha256"]}, POST SHA {links["POSTEXEC.json"]["sha256"]}, reçu SHA {links["receipt.json"]["sha256"]}. Les gros JSON sont parsés intégralement et tous octets référencés hachés ; aucune lecture rawFULL de leur texte ni du binaire olean n'est prétendue. Les sources/outils/audit préparatoires et logs ont été lus FULL selon les reçus existants. Le nouvel olean est une sortie indépendante réelle et lié par tous ses octets.

Baseline officielle avant observation ROOT :74modules/1203auxdéclarations incluant définitions. Proposition conditionnée à cette observation :75/1223. Ce PASS auxiliaire n'acquitte pas un évaluateur spectral uniforme, un calcul certifié du coefficient à10^8, la suppression des puissances premières, H1/C5global, la positivité sur la frontière, D_N, Goldbach ou WIN. Le lot13 est désormais clos immuable ; aucune préparation automatique de lot14.
'''
    new(OWN / "adjudication.md", report)
    completion = {
        "schema": "ROUND22_JUDGE5_COMPLETION_BATCH13", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": receipt["status"], "role": "ROLE5", "actual_child_invocations": 1,
        "modules_passed": 1, "declarations_passed": 20, "module_count_passed": 1, "declaration_count_passed": 20,
        "theorems_passed": 18, "definitions_passed": 2, "all_current_bytes_preserved": True,
        "all_inputs_unchanged": True, "input_count": 7997, "closed_judge_file_count": 861,
        "protected_archive_count": 3089, "capture_count": 25, "print_count": 20,
        "standard_print_count": 20, "recovery_sorryAx_print_count": 0, "declarations_without_axioms": empty,
        "source_sha256": row["source_sha256"], "actual_links": links,
        "adjudication_sha256": sha(OWN / "adjudication.md"), "metadata_close_source_sha256": sha(Path(__file__)),
        "readonly_local_dependencies": ["ThermalProjectionEnvelope22"], "recompiled_dependencies": [],
        "failure_class": None, "analytic_counterexample_observed": False, "parity_obstruction_observed": False,
        "old_batches_recompiled": False, "author_olean_used": False, "retry_count": 0,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "previous_official_modules": 74, "previous_official_declarations": 1203,
        "proposed_new_official_modules": 75, "proposed_new_official_declarations": 1223,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C5_paid": False,
        "global_trace_certified": False, "D_N_paid": False, "WIN": False,
        "full_log_read": "e42839", "full_actual_receipt_read": "b3372a",
        "full_actual_module_receipts_read": "d63e6f"
    }
    new(OWN / "completion_receipt.json", json.dumps(completion, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": completion["status"], "modules_passed": 1, "declarations_passed": 20,
        "all_current_bytes_preserved": True, "adjudication_sha256": sha(OWN / "adjudication.md"),
        "completion_receipt_sha256": sha(OWN / "completion_receipt.json"), "actual_links": links}, sort_keys=True))

if __name__ == "__main__":
    main()
