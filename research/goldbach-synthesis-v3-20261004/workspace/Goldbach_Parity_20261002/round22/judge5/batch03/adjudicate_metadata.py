"""Post-compile document/byte audit only. No subprocess, Lean, or mathematics."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parent.parents[1]
ACTUAL = OWN / "batch03_attempt01"


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def main():
    manifest, catalog = load(OWN / "prepared_manifest.json"), load(OWN / "catalog.json")
    receipt = load(ACTUAL / "receipt.json")
    pre, post = load(ACTUAL / "PREEXEC.json"), load(ACTUAL / "POSTEXEC.json")
    closed = load(OWN / "closed_judge_bindings.json")
    assert receipt["status"] == "INDEPENDENT_BATCH03_AUX_PASS"
    assert receipt["actual_child_invocations"] == 1 and not receipt["hidden_retries"]
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 6597 and len(closed["inputs"]) == 90
    assert len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 21
    assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    for item in pre["inputs"] + closed["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == item["sha256"] == sha(item["capture"])
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"]
    row = receipt["rows"][0]
    assert row == load(ACTUAL / "GammaDerivative22_FIN.json")
    assert row["exit_code"] == 0 and not row["timed_out"] and row["launch_error"] is None
    assert sha(OWN / "sources/GammaDerivative22.lean") == row["source_sha256"]
    assert sha(ACTUAL / "GammaDerivative22.olean") == row["olean_sha256"]
    assert sha(ACTUAL / "GammaDerivative22.stdout.log") == row["stdout_sha256"]
    assert sha(ACTUAL / "GammaDerivative22.stderr.log") == row["stderr_sha256"]
    stdout = (ACTUAL / "GammaDerivative22.stdout.log").read_text(encoding="utf-8")
    stderr = (ACTUAL / "GammaDerivative22.stderr.log").read_text(encoding="utf-8")
    parsed = [{"declaration": name, "axioms": [word.strip() for word in values.replace("\n", " ").split(",") if word.strip()]}
        for name, values in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", stdout + stderr, re.S)]
    assert parsed == row["axiom_rows"]
    assert [item["declaration"] for item in parsed] == catalog["modules"][0]["qualified_prints"]
    assert len(parsed) == 8 and all(set(item["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for item in parsed)
    assert not re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", stdout + stderr)
    assert not stderr and not pre["author_olean_in_lean_path"]
    assert not receipt["old_batches_recompiled"] and not receipt["numeric_bank_replayed"]
    assert not receipt["numeric_PASS_used_as_proof"]
    assert all("role4" not in part for part in pre["LEAN_PATH"].split(";"))
    artifact_names = ("START.json", "GammaDerivative22_START.json", "GammaDerivative22_FIN.json", "FIN.json", "receipt.json",
        "GammaDerivative22.stdout.log", "GammaDerivative22.stderr.log", "GammaDerivative22.olean", "PREEXEC.json", "POSTEXEC.json")
    result = {"schema": "ROUND22_JUDGE5_BATCH03_DOCUMENTARY_ADJUDICATION", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": "INDEPENDENT_BATCH03_AUX_PASS", "scope": "TRUE_GAMMA_DERIVATIVE_AUXILIARY_ONLY", "rows": [row],
        "module_count": 1, "theorem_count": 8, "definition_count": 0, "actual_child_invocations": 1,
        "stdout_FULL_read_chunk": "f912b2", "stderr_FULL_read_chunk": "f912b2", "receipt_FULL_read_chunk": "f912b2",
        "source_FULL_read_chunk": "25c355", "gate_FULL_read_chunk": "45155a",
        "prepost_read_scope": "COMPLETE_JSON_PARSED_AND_ALL_INPUT_BYTES_VERIFIED_NOT_FULL_RAW_DISPLAY",
        "prepost_header_chunk": "ce5de6", "input_bytes_verified": 6597, "closed_judge_bytes_verified": 90,
        "protected_archive_bytes_verified": 3089, "captures_verified": 21, "all_conserved": True,
        "active_source_forbidden_tokens": [], "axiom_rows": parsed, "lint_warning_count": stdout.count("warning:"),
        "paid_statement": "1 <= Re(s) <= 2 implies norm(deriv Complex.Gamma s) <= 19*exp(-(pi/4)*abs(Im(s)))",
        "proof_provenance": "Actual Gamma rotation (independent GammaPrerequisites22), convexity/recurrence, actual holomorphy and mathlib Cauchy derivative estimate on radius1/2",
        "unpaid_target_premises": [], "global_implications": "No H1, C3, C5, Weil identity, infinite contour shift, coefficientN or D_N theorem follows from this auxiliary alone",
        "artifacts": [{"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)} for name in artifact_names],
        "metadata_adjudicator": {"path": str(Path(__file__)), "sha256": sha(Path(__file__))},
        "prior_official_modules": 62, "prior_official_auxiliaries": 1049,
        "proposed_total_after_ROOT_observation_modules": 63, "proposed_total_after_ROOT_observation_auxiliaries": 1057,
        "compiler_invocations_this_adjudication": 0, "mathematical_numeric_invocations": 0, "old_replays": 0,
        "H1_paid": False, "C3_paid": False, "C5_paid": False, "D_N_paid": False, "WIN": False}
    with (OWN / "adjudication.json").open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    document = f"""# Batch03 fermé — Γ′ auxiliaire certifié

INDEPENDENT_BATCH03_AUX_PASS : un seul enfant Lean, exit0. START réel
{row['started_at']} ; FIN compilation {row['finished_at']}. Launcher
6e2cb5/session48108, achèvement b802ea. Les huit théorèmes et huit prints
qualifiés ont été lus FULL f912b2 ; seuls propext, Classical.choice et
Quot.sound apparaissent. Quatre warnings de linter, stderr vide. Aucun
sorry/admit/axiom ajouté, native_decide, unsafe ou preuve par cible supposée.

La conclusion payée est ‖Γ′(s)‖≤19 exp(−π|Im s|/4) pour1≤Re s≤2.
Elle provient de la vraie rotation Γ, du majorant Γ sur la bande élargie,
de la vraie holomorphie et de Cauchy sur un cercle de rayon1/2. Le majorant
189/20 est construit sur la sphère, et189/10≤19 après division par le rayon.
Aucune identité Laplace, intégrabilité ou majoration cible gratuite.

Les6597 entrées,90 fichiers des anciens lots Juge,3089 archives et21 captures
sont revérifiés byte par byte par l'adjudication metadata. PRE/POST sont
entièrement parsés et vérifiés ; aucune lecture brute FULL de ces grands JSON
n'est revendiquée. Aucun ancien compile/replay, probe ou banc numérique.
ΓPrerequisites22 est le propre olean Juge déjà PASS, readonly ; aucun olean
auteur n'est utilisé. Le hash olean égal à celui de l'auteur reflète la sortie
déterministe de l'invocation neuve et ne remplace pas ses traces START/FIN.

Receipt réel : {sha(ACTUAL / 'receipt.json')}.
Olean indépendant : {row['olean_sha256']}.
Log stdout : {row['stdout_sha256']}.
Module FIN : {sha(ACTUAL / 'GammaDerivative22_FIN.json')}.

Delta proposé après observation ROOT :1module/8théorèmes,63modules/1057
déclarations auxiliaires depuis62/1049. H1, C3/C5, trace complète, coefficientN,
D_N et WIN restent ouverts. Le nouveau stage Core19 sera SOURCE seulement
jusqu'à sa gate ROOT distincte ; aucun module du lot fermé ne sera rejoué.
"""
    with (OWN / "completion.md").open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(document)
    print(json.dumps({"status": result["status"], "adjudication_sha256": sha(OWN / "adjudication.json"),
        "completion_sha256": sha(OWN / "completion.md"), "inputs": 6597, "closed_judge": 90, "archives": 3089,
        "captures": 21, "compiler_invocations_this_adjudication": 0, "mathematical_numeric_invocations": 0}))


if __name__ == "__main__":
    main()
