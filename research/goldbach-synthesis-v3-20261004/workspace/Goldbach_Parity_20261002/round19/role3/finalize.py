"""Freeze existing role3 results and stored metadata; no subprocess or mathematics."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import sys
import traceback

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
B = W.parents[1]
REPORT = W.parent / "agent3_formalisation.md"
AUTH = B / ".arbor/sessions/parity/.coordinator/messages/round19_formal3_compile_authorization.json"
AUTH_SHA = "5789edeb0bc1d7c2ff0e0fdacdf05c1f067d60540b8a9bdf30705634bd32d10c"
PREFIX = "GoldbachRound19.RankCalibration."
MODULES = {
    "RankCalibrationFace": (19, 3, 22),
    "RankCalibrationPrice": (24, 7, 31),
    "RankCalibrationArithmetic": (16, 3, 19),
    "RankCalibrationUnitLoss": (8, 1, 9),
    "RankCalibrationEuler": (12, 5, 17),
    "RankCalibrationEstimator": (6, 4, 10),
}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
FAIL_REASONS = {
    1: "Face01 : réécriture de P dans les propres dépendances gcd/quotient ; decide ne réduit pas Squarefree1771.",
    2: "Face02 : réécriture de d dans ses propres gcd/quotients ; corrigée par congrArg₂ sur les seuls opérandes.",
    4: "Price04 : positivité de la branche U vide et cast2≤j alors que log_nonneg attend1≤j.",
    6: "Arithmetic06 : projection non bêta réduite ; déroulements concrets factorization/totient/divisors trop profonds ou non fermés.",
    7: "Arithmetic07 : trois norm_num superflus après rw totient_prime ayant déjà fermé les buts.",
    9: "UnitLoss09 : exact_mod_cast ne traverse pas le front rationnel vers le réel.",
    10: "UnitLoss10 : seule coercion du1 rationnel restait non simplifiée ; Rat.cast_one explicite.",
    12: "Euler12 : simplification de coprimalités/branches conditionnelles ne ferme pas les unités N et les deux termes IE.",
    13: "Euler13 : seule branche de coprimalité N positive reste ouverte ; split K et if_pos/if_neg explicites.",
    15: "Estimator15 : cast A≤J sans simplification de1*J ; chaîne calc triangulaire insuffisamment typée pour Trans.",
    16: "Estimator16 : inégalité finale devenue identique après simp only mais non fermée automatiquement ; le_rfl explicite.",
}


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exclusive(path, payload):
    with Path(path).open("xb") as out:
        out.write(payload)


def exclusive_json(path, obj):
    exclusive(path, (json.dumps(obj, indent=2, ensure_ascii=False) + "\n").encode("utf-8"))


def verify(path, digest):
    assert sha(path) == digest, ("frozen_binding_changed", str(path))


def main():
    for name in ("manifest.json", "final_receipt.json", "finalize_started.json"):
        assert not (W / name).exists(), ("metadata_finalization_is_exclusive", name)
    own = Path(__file__).resolve()
    exclusive(W / "finalize_source_PREEXEC.py.txt", own.read_bytes())
    exclusive_json(W / "finalize_started.json", {
        "phase": "PREEXEC", "started_utc": now(),
        "command": [sys.executable, "-B", "-X", "utf8", str(own)], "cwd": str(W),
        "operation": "Bind stored logs, captures, sources and oleans only; no Lean/numeric/Judge",
        "source_sha256": sha(own), "source_snapshot_sha256": sha(W / "finalize_source_PREEXEC.py.txt"),
        "report_DRAFT_sha256": sha(REPORT), "build_receipt_sha256": sha(W / "build_receipt.json"),
    })
    verify(AUTH, AUTH_SHA)
    auth = json.loads(AUTH.read_text(encoding="utf-8"))
    assert auth["compile_authorization_token"] == "ROOT19_FORMAL3_COMPILE"
    for rel, digest in auth["checked_inputs_sha256"].items():
        verify(B / rel, digest)
    ledger = json.loads((W / "build_receipt.json").read_text(encoding="utf-8"))
    assert ledger["old_Lean_rebuilds"] == ledger["old_producers_replayed"] == ledger["old_oleans_copied"] == 0
    assert ledger["victory"] is False
    attempts = ledger["attempts"]
    assert [a["attempt"] for a in attempts] == list(range(1, len(attempts) + 1))
    readonly = {}
    for a in attempts:
        assert a["state"] == "FINISHED" and a["exit_code"] in (0, 1)
        assert a["authorization_sha256"] == AUTH_SHA
        for field in ("source_capture", "launcher_capture", "authorization_capture", "log"):
            verify(a[field], a[field + "_sha256"])
        assert a["source_sha256"] == a["source_capture_sha256"]
        assert a["checked_numeric_inputs_sha256"] == auth["checked_inputs_sha256"]
        for path, digest in a["readonly_imports_sha256"].items():
            verify(path, digest)
            if "round18" in Path(path).parts:
                readonly[Path(path).relative_to(B).as_posix()] = digest
        if a["exit_code"] == 0:
            verify(a["olean"], a["olean_sha256"])
            verify(a["preserved_olean"], a["preserved_olean_sha256"])
            assert a["olean_sha256"] == a["preserved_olean_sha256"]
    records = []
    for module, (thms, defs, prints) in MODULES.items():
        passed = [a for a in attempts if a["module"] == module and a["exit_code"] == 0]
        assert len(passed) == 1, ("no_missing_or_replayed_PASS", module)
        a = passed[0]
        source = W / (module + ".lean")
        verify(source, a["source_sha256"])
        text = source.read_text(encoding="utf-8")
        code = text.split("-- AXIOM_AUDIT_BEGIN")[0]
        assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustMe)\b", code)
        names = re.findall(r"^(?:def|theorem|lemma|structure)\s+([A-Za-z][A-Za-z0-9_']*)", code, re.M)
        expected = re.findall(r"^#print axioms (\S+)\s*$", text, re.M)
        assert expected == [PREFIX + n for n in names]
        assert len(re.findall(r"^theorem\s", code, re.M)) == thms
        assert len(re.findall(r"^def\s", code, re.M)) == defs
        assert len(expected) == prints
        log = Path(a["log"]).read_text(encoding="utf-8")
        assert not re.search(r"(?:sorryAx\b|error:)", log)
        printed = re.findall(r"(?m)^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
        assert [n for n, _ in printed] == expected
        axioms = []
        for name, axiom_text in printed:
            terms = [v.strip() for v in axiom_text.split(",") if v.strip()]
            assert set(terms) <= STANDARD, ("nonstandard_axiom", name, terms)
            axioms.append({"name": name, "axioms": terms})
        warnings = [line for line in log.splitlines() if "warning:" in line]
        records.append({"module": module + ".lean", "namespace": PREFIX[:-1],
            "producer_first_PASS_attempt": a["attempt"], "source_sha256": a["source_sha256"],
            "olean_sha256": a["olean_sha256"], "log_sha256": a["log_sha256"],
            "theorems_explicit": thms, "definitions": defs, "structures": 0,
            "axiom_prints": axioms, "warnings": warnings})
    failed = [a for a in attempts if a["exit_code"] != 0]
    assert set(FAIL_REASONS) == {a["attempt"] for a in failed}, "Report must describe every actual failure"
    failures = [{"attempt": a["attempt"], "module": a["module"], "reason": FAIL_REASONS[a["attempt"]],
        "log_sha256": a["log_sha256"], "source_capture_sha256": a["source_capture_sha256"],
        "actual_start_utc": a["started_at_utc"], "actual_finish_utc": a["finished_at_utc"]} for a in failed]
    lines = ["# FINAL3 — prix de calibration de rang, node13.11", "",
        "Six nouveaux modules ont un PASS auteur réel. 85 théorèmes explicites,23 définitions,108 prints d'axiomes standards ou aucun axiome. Aucun sorry/admit/axiome libre/native_decide/trustMe dans les sources compilées. Score0, victory=false ; le Juge indépendant n'a pas encore certifié ces résultats.", "",
        f"Le lanceur a exécuté {len(attempts)} invocations Lean réelles :6 PASS et{len(failed)} FAIL techniques. Chaque tentative conserve source, lanceur, gate, commande/environnement/imports PREEXEC, puis log/exit/reçu et chaque PASS olean préservé. Aucun ancien Lean/producteur, aucun PASS inchangé rejoué, aucune copie d'olean historique. Les quatre dépendances18 restent en lecture seule. La gate concrète lie le PASS numérique rank19 unique ; aucune production numérique par ROLE3.", "",
        "| Module | PASS réel | Théorèmes | Définitions | Prints |", "|---|---:|---:|---:|---:|"]
    lines += [f"| {r['module']} | {r['producer_first_PASS_attempt']} | {r['theorems_explicit']} | {r['definitions']} | {len(r['axiom_prints'])} |" for r in records]
    lines += ["", "Les trois warnings simpa de UnitLoss lignes25/26/29 sont bénins et conservés. Aucun module PASS n'est rejoué pour les supprimer. Les autres logs PASS sont sans warning.", "", "Échecs réels et corrections :", ""]
    lines += ["- " + FAIL_REASONS[a["attempt"]] for a in failed]
    lines += ["", "Les prints des déclarations ratées utilisent sorryAx interne dans leurs logs d'échec ; ces tentatives ne sont pas des PASS. Les correctifs concernent élaboration, réécritures, calculs kernel et casts. Aucun contre-exemple à l'identité physique, aucun échec de parité n'est inventé à partir de ces erreurs techniques.", "",
        "Face dérive l'exclusion sur le vrai PhysicalWitness18 de la face de trois petits premiers, le quotient P/gcd(P,d), les overlaps, le support A≤J' et la branche vide. Price conserve Gamma0=Gamma_rank+Eunit+Lrank, références réelles, theta/raw/properpowers et K6 avec le facteur A·lost/J. Arithmetic dérive les modules≤max(aR,R^4), la reconstruction squarefree d,k avec repeats et la multiplicité≤32 dans une expansion unique, ainsi que chi réel de totient et son minimum451/2336400. Ce lemme32 ne prouve pas le plafond combiné40/64 des trois développements.", "",
        "UnitLoss dérive les seuls facteurs c/r>R perdus, les fronts+1 et une majoration de leur prix theta grâce au support physique. Euler conserve tous les diviseurs originaux, y compris Möbius nul, retire les seuls termes non unitaires à N arithmétiquement nuls, puis définit les restes effectifs. Estimator dérive l'identité exacte autour de −M·chi et sa borne triangulaire avec erreurs de normalisation et vrais restes. M est une expression réelle ; sa positivité effective n'est pas postulée ou démontrée dans cette portée.", "",
        "K14 complet, positivité du coefficient IE effectif, raccord des restes unitaires aux AP ordinaires/endpoints et exceptions, multiplicité combinée source40/64, K17/K18 source, constantes/onset BV et application au seul logN≥10^24 restent ouverts. Gamma_rank peut augmenter du principal négatif opposé au prix ; aucune minoration de capacité ou petite Gamma n'est ajoutée comme prémisse. Comparaisons parents, autres familles, medium/longs, union physique des capacités et ledger entier restent impayés. La cible D_N≤N/(256logNloglogN) n'est donc pas prouvée.", "",
        "Le cadre et les1361 archives restent inchangés. PREPARATION_REVIEW.md et preparation.json sont préservés. Le rapport3 était absent lors de la reprise ; le DRAFT nouveau est capturé dans agent3_DRAFT_PRE_FINAL.md.txt avant ce FINAL. La finalisation ne lit que les artefacts existants et ne lance ni Lean, ni producteur, ni Juge.", ""]
    stage = ("\n".join(lines)).encode("utf-8")
    exclusive(W / "report_FINAL_ready.md.txt", stage)
    exclusive(W / "agent3_DRAFT_PRE_FINAL.md.txt", REPORT.read_bytes())
    REPORT.write_bytes(stage)
    finished = now()
    exclusive(W / "finalize.log", (f"Metadata only; existing attempts {len(attempts)}, PASS6, FAIL{len(failed)}; no subprocess.\nSix sources/oleans and108 standard/empty axiom prints bound.\nThree benign UnitLoss warnings retained.\nScore0; noWin; independent Judge pending.\nFinished UTC {finished}\n").encode("utf-8"))
    bindings = {p.relative_to(B).as_posix(): sha(p) for p in sorted(W.rglob("*")) if p.is_file() and p.name not in {"manifest.json", "final_receipt.json"}}
    bindings[REPORT.relative_to(B).as_posix()] = sha(REPORT)
    manifest = {"status": "FINAL", "round": 19, "role": 3, "node_id": "13.11", "finished_utc": finished,
        "producer_module_PASS_count": 6, "producer_Lean_executions": len(attempts),
        "producer_Lean_FAIL_technical_count": len(failed), "historical_recompiles": 0, "PASS_reruns": 0,
        "definitions": 23, "explicit_theorems": 85, "structures": 0, "axiom_print_count": 108,
        "modules": records, "actual_failures": failures, "bindings": bindings,
        "readonly_dependency_bindings": readonly, "numeric_gate_bindings": auth["checked_inputs_sha256"],
        "root_gate_path": AUTH.relative_to(B).as_posix(), "root_gate_sha256": AUTH_SHA,
        "score": 0, "victory": False, "independent_Judge_pending": True,
        "unpaid": ["K14 positivity effective", "combined source multiplicity40/64", "ordinary AP conversion", "K17/K18 source", "BV constants/onset", "Gamma_rank", "parents", "other families", "capacity", "full ledger", "D_N target"]}
    exclusive_json(W / "manifest.json", manifest)
    receipt = {"status": "FINAL", "round": 19, "role": 3, "node_id": "13.11", "finished_utc": finished,
        "exit_code": 0, "operation": "Bind and freeze existing results only",
        "metadata_command": [sys.executable, "-B", "-X", "utf8", str(own)],
        "manifest_sha256": sha(W / "manifest.json"), "report_sha256": sha(REPORT),
        "build_receipt_sha256": sha(W / "build_receipt.json"), "finalize_log_sha256": sha(W / "finalize.log"),
        "finalize_source_PREEXEC_sha256": sha(W / "finalize_source_PREEXEC.py.txt"),
        "finalize_started_sha256": sha(W / "finalize_started.json"), "bound_files": len(bindings),
        "producer_Lean_executions": len(attempts), "producer_PASS_count": 6, "producer_FAIL_count": len(failed),
        "new_Lean_executions_in_finalization": 0, "new_numeric_executions_in_finalization": 0,
        "Judge_executions": 0, "score": 0, "victory": False, "independent_Judge_pending": True}
    exclusive_json(W / "final_receipt.json", receipt)
    print(json.dumps({"final_receipt_sha256": sha(W / "final_receipt.json"), **receipt}, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        trace = traceback.format_exc()
        exclusive(W / "finalize_failed01.log", trace.encode("utf-8"))
        exclusive_json(W / "finalize_failed01_receipt.json", {"finished_utc": now(), "exit_code": 1,
            "operation": "Metadata only, no Lean/numeric/Judge", "source_sha256": sha(Path(__file__)),
            "log_sha256": sha(W / "finalize_failed01.log")})
        print(trace, file=sys.stderr)
        raise SystemExit(1)
