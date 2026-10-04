"""Bind existing ROLE4 results only. No Lean, numeric producer, or Judge invocation."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import sys
import traceback

W = Path(__file__).resolve().parent
B = W.parent.parent
REPORT = W.parent / "agent4_formalisation.md"
STAGE = W / "report_FINAL_ready.md.txt"
MODULES = {
    "TerminalPrimeExtraction.lean": ("GoldbachRound19.Terminal", 2, 18, 4, 0, 22),
    "BalancedResourceSwitch.lean": ("GoldbachRound19.Switch", 5, 25, 13, 2, 41),
    "SignedHyperbolicCRT.lean": ("GoldbachRound19.SignedCRT", 7, 19, 13, 1, 34),
    "NonSSBracketSwitch.lean": ("GoldbachRound19.NonSS", 9, 21, 18, 0, 39),
    "RankTwoHarmonic.lean": ("GoldbachRound19.Harmonic", 12, 17, 7, 0, 24),
}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def exclusive(p, data):
    with Path(p).open("xb") as f:
        f.write(data)


def exclusive_json(p, obj):
    exclusive(p, (json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))


def verify(p, expected):
    actual = sha(p)
    if actual != expected:
        raise ValueError(f"SHA mismatch: {p}: {actual} != {expected}")


def lean_without_comments(source):
    # Lean supports nested block comments. Preserve only active source for token checks.
    result = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unterminated Lean comment")
    return "".join(result)


def main():
    for name in ("manifest.json", "final_receipt.json", "finalize_started.json"):
        if (W / name).exists():
            raise RuntimeError(f"Finalization is exclusive, refusing replay: {name}")
    own = W / "finalize.py"
    exclusive(W / "finalize_source_PREEXEC.py.txt", own.read_bytes())
    exclusive_json(W / "finalize_started.json", {
        "phase": "PREEXEC",
        "started_utc": now(),
        "scope": "Metadata binding of existing compiled modules; no Lean/numeric/Judge",
        "command": [sys.executable, "-B", "-X", "utf8", str(own)],
        "cwd": str(W),
        "source_sha256": sha(own),
        "source_snapshot": str(W / "finalize_source_PREEXEC.py.txt"),
        "source_snapshot_sha256": sha(W / "finalize_source_PREEXEC.py.txt"),
        "build_receipt_sha256": sha(W / "build_receipt.json"),
        "report_stage_sha256": sha(STAGE),
        "report_DRAFT_sha256": sha(REPORT),
    })
    ledger = json.loads((W / "build_receipt.json").read_text(encoding="utf-8"))
    gate_path = W / "root_compile_authorization.json"
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    gate_hash = sha(gate_path)
    verify(gate_path, "6ccdfc20f4a95fc84733532b83cb3d0f773378ec11504b40a48c83d026026a5d")
    assert gate["authorization"] == "ROOT19_FORMAL4_COMPILE"
    assert gate["root_authorized"] is True
    assert gate["canonical_new_numeric_pass_inspected"] is True
    for rel, digest in gate["numeric_bindings"].items():
        verify(B / rel, digest)
    deps_path = W / "dependencies_readonly.json"
    deps = json.loads(deps_path.read_text(encoding="utf-8"))
    assert len(deps["bindings"]) == 10
    for rel, digest in deps["bindings"].items():
        verify(B / rel, digest)
    assert ledger["historical_source_compiles"] == 0
    assert ledger["score"] == 0 and ledger["victory"] is False
    attempts = ledger["attempts"]
    assert len(attempts) == 12
    assert [a["attempt"] for a in attempts] == list(range(1, 13))
    for a in attempts:
        assert a["phase"] == "FINISHED"
        assert a["exit_code"] in (0, 1)
        assert a["compile_gate_sha256"] == gate_hash
        assert a["dependency_bindings"] == deps["bindings"]
        assert a["numeric_bindings"] == gate["numeric_bindings"]
        verify(a["snapshot"], a["snapshot_sha256"])
        assert a["snapshot_sha256"] == a["source_sha256"]
        verify(a["builder_snapshot"], a["builder_snapshot_sha256"])
        verify(a["started_receipt"], a["started_receipt_sha256"])
        verify(a["log"], a["log_sha256"])
        for p, digest in a["new_import_bindings"].items():
            verify(p, digest)
        if a["exit_code"] == 0:
            verify(a["olean"], a["olean_sha256"])
    assert set(ledger["successful_modules"]) == set(MODULES)
    assert sum(a["exit_code"] == 0 for a in attempts) == 5
    assert sum(a["exit_code"] != 0 for a in attempts) == 7
    module_records = []
    for name, (namespace, attempt_id, thms, defs, structures, prints) in MODULES.items():
        frozen = ledger["successful_modules"][name]
        assert frozen["attempt"] == attempt_id
        verify(frozen["source"], frozen["source_sha256"])
        verify(frozen["olean"], frozen["olean_sha256"])
        source = Path(frozen["source"]).read_text(encoding="utf-8")
        active = lean_without_comments(source)
        assert not re.search(r"\b(?:sorry|admit|native_decide|trustMe)\b", active)
        assert not re.search(r"(?m)^\s*(?:opaque\s+)?axiom\s", active)
        assert len(re.findall(r"(?m)^theorem\s", active)) == thms
        assert len(re.findall(r"(?m)^def\s", active)) == defs
        assert len(re.findall(r"(?m)^(?:@\[[^\]\n]+\]\s+)?structure\s", active)) == structures
        expected_names = [namespace + "." + n for n in
                          re.findall(r"(?m)^#print axioms\s+(\S+)\s*$", active)]
        assert len(expected_names) == prints
        a = attempts[attempt_id - 1]
        log = Path(a["log"]).read_text(encoding="utf-8")
        assert not re.search(r"(?:sorryAx\b|warning:|error:)", log)
        axiom_records = []
        printed = re.findall(
            r"(?m)^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
            log,
        )
        assert [name for name, _ in printed] == expected_names
        for theorem_name, axiom_text in printed:
            axioms = [v.strip() for v in axiom_text.split(",") if v.strip()]
            assert set(axioms) <= STANDARD
            axiom_records.append({"name": theorem_name, "axioms": axioms})
        module_records.append({
            "module": name,
            "namespace": namespace,
            "producer_first_PASS_attempt": attempt_id,
            "source_sha256": frozen["source_sha256"],
            "olean_sha256": frozen["olean_sha256"],
            "log_sha256": a["log_sha256"],
            "theorems_explicit": thms,
            "definitions": defs,
            "structures": structures,
            "axiom_prints": axiom_records,
        })
    exclusive(W / "agent4_DRAFT_PRE_FINAL.md.txt", REPORT.read_bytes())
    # The final report is the only file replaced. Compiled sources and oleans remain untouched.
    REPORT.write_bytes(STAGE.read_bytes())
    finished = now()
    log_text = (
        f"Metadata finalization started: {(W / 'finalize_started.json').name}\n"
        "Existing producer Lean executions: 12; PASS 5; FAIL 7\n"
        "Prior Python parser failure: 1; Lean executions contributed: 0\n"
        "Modules: 5; explicit theorems: 100; definitions: 55; structures: 3; axiom prints: 160\n"
        "All final printed axioms are standard or empty; all SHA bindings match\n"
        "Historical recompiles: 0; PASS reruns: 0; new Lean/numeric/Judge invocations during finalization: 0\n"
        "Score: 0; victory: false; independent Judge pending\n"
        f"Finished UTC: {finished}\nExit code: 0\n"
    )
    exclusive(W / "finalize.log", log_text.encode("utf-8"))
    bindings = {}
    for p in sorted(W.rglob("*")):
        if p.is_file() and p.name not in {"manifest.json", "final_receipt.json"}:
            bindings[p.relative_to(B).as_posix()] = sha(p)
    bindings[REPORT.relative_to(B).as_posix()] = sha(REPORT)
    manifest = {
        "status": "FINAL",
        "round": 19,
        "role": 4,
        "node_id": "14.4",
        "finished_utc": finished,
        "producer_module_PASS_count": 5,
        "producer_Lean_executions": 12,
        "producer_Lean_FAIL_technical_count": 7,
        "prior_Python_parse_failure_count": 1,
        "historical_recompiles": 0,
        "PASS_reruns": 0,
        "definitions": 55,
        "explicit_theorems": 100,
        "structures": 3,
        "generated_ext_lemmas_printed": 2,
        "axiom_print_count": 160,
        "scope": "Producer auxiliary formalization only; independent Judge pending",
        "score": 0,
        "victory": False,
        "modules": module_records,
        "bindings": bindings,
        "readonly_dependency_bindings": deps["bindings"],
        "numeric_gate_bindings": gate["numeric_bindings"],
        "unpaid": ["H7 analytic", "H9 rank3short at u>=10^40", "source onset u>=10^24 unchanged",
                   "rank>=4", "medium and long conductors", "Gamma", "capacity", "T_A", "full ledger", "D_N target"],
    }
    exclusive_json(W / "manifest.json", manifest)
    final = {
        "status": "FINAL",
        "round": 19,
        "role": 4,
        "node_id": "14.4",
        "finished_utc": finished,
        "exit_code": 0,
        "operation": "Bind and freeze existing producer results only",
        "metadata_command": [sys.executable, "-B", "-X", "utf8", str(own)],
        "manifest_sha256": sha(W / "manifest.json"),
        "report_sha256": sha(REPORT),
        "build_receipt_sha256": sha(W / "build_receipt.json"),
        "finalize_log_sha256": sha(W / "finalize.log"),
        "finalize_source_PREEXEC_sha256": sha(W / "finalize_source_PREEXEC.py.txt"),
        "finalize_started_sha256": sha(W / "finalize_started.json"),
        "producer_Lean_executions": 12,
        "producer_PASS_count": 5,
        "producer_FAIL_count": 7,
        "new_Lean_executions_in_finalization": 0,
        "new_numeric_executions_in_finalization": 0,
        "Judge_executions": 0,
        "score": 0,
        "victory": False,
        "independent_Judge_pending": True,
    }
    exclusive_json(W / "final_receipt.json", final)
    print(json.dumps({"final_receipt_sha256": sha(W / "final_receipt.json"),
                      "manifest_sha256": final["manifest_sha256"],
                      "report_sha256": final["report_sha256"],
                      "module_sources": {v["module"]: v["source_sha256"] for v in module_records},
                      "score": 0, "victory": False}, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        failure = traceback.format_exc()
        failure_path = W / "finalize_failed01.log"
        if not failure_path.exists():
            exclusive(failure_path, failure.encode("utf-8"))
            exclusive_json(W / "finalize_failed01_receipt.json", {
                "finished_utc": now(), "exit_code": 1,
                "operation": "Metadata binding only; no Lean/numeric/Judge",
                "source_sha256": sha(W / "finalize.py"),
                "log_sha256": sha(failure_path),
            })
        print(failure, file=sys.stderr)
        raise SystemExit(1)
