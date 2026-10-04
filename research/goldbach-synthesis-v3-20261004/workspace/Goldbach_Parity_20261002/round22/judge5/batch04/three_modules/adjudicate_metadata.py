"""Documentary closure after the authorized three children; no compiler or maths."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
BASE = OWN.parents[1].parents[1]
ACTUAL = OWN / "batch04_attempt01"
MODULES = ("GammaPsiCore22", "GammaPsiBetaLimit22", "GammaPsiIntegral22")


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
    receipt, pre, post = load(ACTUAL / "receipt.json"), load(ACTUAL / "PREEXEC.json"), load(ACTUAL / "POSTEXEC.json")
    closed = load(OWN / "closed_judge_bindings.json")
    assert receipt["status"] == "INDEPENDENT_BATCH04_AUX_PASS"
    assert receipt["actual_child_invocations"] == 3 and not receipt["hidden_retries"]
    assert tuple(row["module"] for row in receipt["rows"]) == MODULES
    assert pre["inputs"] == post["inputs"] == manifest["immutable_inputs"]
    assert pre["protected_archives"] == post["protected_archives"]
    assert len(pre["inputs"]) == 6648 and len(closed["inputs"]) == 134
    assert len(pre["protected_archives"]) == 3089 and len(pre["captures"]) == 26
    assert post["all_inputs_unchanged"] and post["captures_unchanged"] and post["gate_unchanged"]
    for item in pre["inputs"] + closed["inputs"]:
        assert sha(item["path"]) == item["sha256"], item["path"]
    for item in pre["protected_archives"]:
        assert sha(BASE / item["path"]) == item["sha256"], item["path"]
    for item in pre["captures"]:
        assert sha(item["source"]) == item["sha256"] == sha(item["capture"])
    assert sha(pre["gate_path"]) == pre["gate_sha256"] == post["gate_sha256"]
    assert not pre["author_olean_in_lean_path"] and not receipt["author_olean_used"]
    assert not receipt["old_batches_recompiled"] and not receipt["numeric_bank_replayed"]
    assert not receipt["numeric_PASS_used_as_proof"] and receipt["readonly_local_dependencies"] == []
    paths = pre["LEAN_PATH"].split(";")
    assert Path(paths[0]) == ACTUAL and len(paths) == 9
    assert all("role3" not in path and "role4" not in path and "batch03" not in path for path in paths)
    axioms, warnings, bindings = [], {}, []
    for row, info, expected_count in zip(receipt["rows"], catalog["modules"], (19, 23, 10)):
        module = row["module"]
        assert row == load(ACTUAL / (module + "_FIN.json"))
        assert row["exit_code"] == 0 and not row["timed_out"]
        assert row["status"] == "INDEPENDENT_LEAN_AUX_PASS" and row["exact_axiom_coverage_standard_only"]
        assert sha(info["source"]) == row["source_sha256"]
        assert sha(ACTUAL / (module + ".olean")) == row["olean_sha256"]
        log = (ACTUAL / (module + ".log")).read_text(encoding="utf-8")
        assert sha(ACTUAL / (module + ".log")) == row["log_sha256"]
        parsed = [{"declaration": name, "axioms": [word.strip() for word in values.replace("\n", " ").split(",") if word.strip()]}
            for name, values in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S)]
        assert parsed == row["axiom_rows"] and len(parsed) == expected_count
        assert [item["declaration"] for item in parsed] == info["qualified_prints"]
        assert all(set(item["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for item in parsed)
        assert not re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", log)
        axioms += parsed
        warnings[module] = log.count("warning:")
        for name in (module + "_START.json", module + "_FIN.json", module + ".log", module + ".olean"):
            bindings.append({"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)})
    assert len(axioms) == 52 and len({item["declaration"] for item in axioms}) == 52
    assert catalog["theorem_count"] == 44 and catalog["definition_count"] == 8
    for name in ("START.json", "FIN.json", "receipt.json", "PREEXEC.json", "POSTEXEC.json"):
        bindings.append({"path": str(ACTUAL / name), "sha256": sha(ACTUAL / name)})
    charges = {
        "Core": "Actual Gamma derivative/recurrence/nonvanishing, true quotient derivative at zero, slope limit and positive-parameter Beta integrability",
        "Beta_majorant": "2*(t^(Re(z)-1)+1)+norm(z-1)*(1+(1/2)^(Re(z)-2)); integrable for Re(z)>0, uniform for w>=0",
        "Beta_DCT": "Actual a.e. measurability, pointwise limit and explicit integrable majorant proved; no free Integrable or dominance premise",
        "Integral_Jacobian": "t=exp(-u) image (0,infinity)->(0,1), injectivity, derivative -exp(-u), absolute Jacobian, actual cpow identity",
        "Integral_integrability": "Transported from the proved beta-integrand integrability for Re(z)>0 before final P1",
        "totalized_intermediate": "Change-of-variable equality for arbitrary z uses Bochner totalization; final Re(z)>0 theorem has separately proved integrability",
    }
    result = {"schema": "ROUND22_JUDGE5_BATCH04_DOCUMENTARY_ADJUDICATION", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": "INDEPENDENT_BATCH04_AUX_PASS", "scope": "ACTUAL_GAMMA_PSI_P1_AUXILIARY_ONLY", "rows": receipt["rows"],
        "module_count": 3, "theorem_count": 44, "definition_count": 8, "declarations": 52, "actual_child_invocations": 3,
        "logs_START_FIN_receipt_FULL_read_chunk": "8657fd", "source_FULL_read_chunk": "22254c", "gate_FULL_read_chunk": "c24860",
        "prepost_read_scope": "COMPLETE_JSON_PARSED_AND_ALL_INPUT_BYTES_VERIFIED_NOT_FULL_RAW_DISPLAY", "prepost_header_chunk": "49289b",
        "input_bytes_verified": 6648, "closed_judge_bytes_verified": 134, "protected_archive_bytes_verified": 3089,
        "captures_verified": 26, "all_conserved": True, "active_source_forbidden_tokens": [], "axiom_rows": axioms,
        "lint_warning_counts": warnings, "analytic_charges": charges, "unpaid_target_premises": [],
        "P1_independently_certified": True,
        "paid_statement": "For Re(z)>0: deriv(Gamma,z)/Gamma(z) = -EulerGamma + integral(u>0,(exp(-u)-exp(-z*u))/(1-exp(-u))) and integrability of that actual integrand",
        "global_gaps": ["Test-function pairing and global Fubini/Arch C5", "Duplication (outside frozen lot)", "Weil/global trace identity", "Infinite contour shift and complete zero count", "coefficientN", "D_N target"],
        "artifacts": bindings, "metadata_adjudicator": {"path": str(Path(__file__)), "sha256": sha(Path(__file__))},
        "prior_independent_modules": 63, "prior_independent_auxiliaries": 1057,
        "proposed_total_after_ROOT_observation_modules": 66, "proposed_total_after_ROOT_observation_auxiliaries": 1109,
        "compiler_invocations_this_adjudication": 0, "mathematical_numeric_invocations": 0, "old_replays": 0,
        "H1_paid": False, "C3_paid": False, "C5_paid": False, "D_N_paid": False, "WIN": False}
    with (OWN / "adjudication.json").open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    times = "\n".join(f"- {row['module']} : {row['started_at']} → {row['finished_at']}, exit0." for row in receipt["rows"])
    document = f"""# Batch04 clos — vraie P1 auxiliaire certifiée

INDEPENDENT_BATCH04_AUX_PASS : trois enfants neufs Core→BetaLimit→Integral,
52prints exacts,44théorèmes et8définitions. Launcher841fed/session76496,
achèvement431075 exit0. Gate réelle {pre['gate_sha256']}.
Logs, START, FIN et receipt lus FULL8657fd, sans troncature.

{times}

Tous les prints ne dépendent que de propext, Classical.choice et Quot.sound.
Core porte quatre warnings de linter ; BetaLimit et Integral aucun. Aucun
sorry/admit/axiom ajouté, native_decide, unsafe ou cible supposée. Les trois
oleans sont produits dans le nouveau dossier du lot ; les imports locaux des
deux derniers utilisent ces sorties neuves. Aucun olean auteur, ancien compile,
retry, probe ou banc numérique. Des SHA identiques aux sorties auteurs n'effacent
pas la provenance distincte des nouvelles commandes START/FIN.

La conclusion P1 payée est, pour Re z>0,
Γ′(z)/Γ(z)=−γ_E+∫_(u>0)(exp(−u)−exp(−zu))/(1−exp(−u))du,
avec intégrabilité du véritable intégrande. Core identifie le vrai quotient Γ
et sa limite ; BetaLimit construit le majorant concret intégrable
2(t^(Re z−1)+1)+‖z−1‖(1+(1/2)^(Re z−2)), sa mesurabilité et DCT.
Integral prouve l'image, l'injectivité, la dérivée signée et le Jacobien absolu
de t=exp(−u), puis transporte l'intégrabilité avant la conclusion. Aucune
prémisse libre de domination, intégrabilité ou formule Ψ cible. L'égalité
intermédiaire pour tout z emploie l'intégrale Bochner totalisée ; le domaine
Re z>0 est payé séparément pour donner la véritable identité intégrable.

L'adjudication documentaire revérifie les6648 entrées,134 anciens fichiers
Juge,3089 archives et26 captures byte par byte, plus la gate. PRE/POST sont
entièrement parsés et liés ; aucune lecture brute FULL des grands JSON ou FULL
mathématique de toute la fermeture n'est revendiquée. Conservations vraies.
Receipt : {sha(ACTUAL / 'receipt.json')}.

Delta proposé après observation ROOT :3modules/52déclarations,66/1109 depuis
63/1057. Cette P1 auxiliaire ne paie pas le couplage à la fonction test, le
Fubini global/C5, duplication horslot, Weil, contours infinis, compte complet
des zéros, coefficientN, D_N ou WIN. Aucun autre compilateur anticipé.
"""
    with (OWN / "completion.md").open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(document)
    print(json.dumps({"status": result["status"], "adjudication_sha256": sha(OWN / "adjudication.json"),
        "completion_sha256": sha(OWN / "completion.md"), "inputs": 6648, "closed_judge": 134, "archives": 3089,
        "captures": 26, "declarations": 52, "P1_independently_certified": True,
        "compiler_invocations_this_adjudication": 0, "mathematical_numeric_invocations": 0}))


if __name__ == "__main__":
    main()
