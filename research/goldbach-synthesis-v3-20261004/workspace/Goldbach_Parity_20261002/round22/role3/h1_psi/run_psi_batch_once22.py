"""SOURCE ONLY launcher: one root-bound author batch; stop at first failure.

This program is not a mathematical evaluator. It invokes only the four listed
Lean modules once, when the actual numeric observation and a root gate are bound.
Preparation of this source does not authorize execution.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROLE = Path(__file__).resolve().parent
BASE = ROLE.parents[2]
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
MODULES = ("GammaPsiCore22", "GammaPsiBetaLimit22", "GammaPsiIntegral22", "GammaPsiDuplication22")
COUNTS = (19, 23, 10, 2)
GAMMA_DIR = BASE / "round22" / "judge5" / "batch02_attempt01"
GAMMA_SHA = "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            h.update(block)
    return h.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def write_new(path, obj):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(obj, stream, indent=2, ensure_ascii=False, sort_keys=True)
        stream.write("\n")


def audit_axioms(log, expected):
    rows = []
    for line in log.splitlines():
        hit = re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]", line)
        empty = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if hit:
            rows.append({"declaration": hit[1], "axioms": [s.strip() for s in hit[2].split(",") if s.strip()]})
        elif empty:
            rows.append({"declaration": empty[1], "axioms": []})
    names = [row["declaration"] for row in rows]
    ok = (len(names) == len(expected) and set(names) == set(expected)
          and len(set(names)) == len(names)
          and all(set(row["axioms"]) <= ALLOWED_AXIOMS for row in rows)
          and "sorryAx" not in log)
    return rows, ok


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gate", required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if args.attempt != "psi_batch01_attempt01":
        raise RuntimeError("only the first frozen author batch is implemented")
    manifest_path = ROLE / "psi_source_manifest22.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    gate_path = Path(args.gate).resolve()
    if gate_path.parent != (BASE / ".arbor" / "sessions" / "parity" / ".coordinator" / "messages").resolve():
        raise RuntimeError("the gate must be an actual root-owned coordinator/messages file")
    gate = json.loads(gate_path.read_text(encoding="utf-8-sig"))
    numeric = manifest["numeric_evidence"]
    if numeric["numeric_PASS"] is not False or numeric["counterexample_established"] is not False:
        raise RuntimeError("the prepared observation must not invent a numeric PASS or suppress a counterexample")
    requirements = {
        "role": "ROLE3", "node_id": "15.3", "stage": "H1_PSI_BATCH01",
        "attempt": args.attempt, "authorized": True, "modules": list(MODULES),
        "numeric_pass_required": False, "numeric_PASS": False, "numeric_counterexample_established": False,
        "numeric_receipt_sha256": numeric["receipt_sha256"], "numeric_receipt_exit_code": 1,
        "source_manifest_sha256": sha(manifest_path), "launcher_sha256": sha(Path(__file__)),
        "python_sha256": PYTHON_SHA, "lean_sha256": LEAN_SHA, "no_win": True,
        "readonly_gamma_olean_sha256": GAMMA_SHA,
    }
    for key, value in requirements.items():
        if gate.get(key) != value:
            raise RuntimeError("root gate mismatch: " + key)
    if (Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN) != LEAN_SHA
            or not sys.flags.dont_write_bytecode or sys.flags.utf8_mode != 1):
        raise RuntimeError("canonical runtime binding mismatch")
    if sha(GAMMA_DIR / "GammaPrerequisites22.olean") != GAMMA_SHA:
        raise RuntimeError("readonly independently audited Gamma dependency changed")
    receipt = json.loads(Path(numeric["receipt_path"]).read_text(encoding="utf-8-sig"))
    if (sha(numeric["receipt_path"]) != numeric["receipt_sha256"] or receipt.get("exit_code") != 1
            or receipt.get("result_sha256") is not None or receipt.get("post_integrity") is not True):
        raise RuntimeError("the actual technical export failure observation changed")
    if manifest["modules"] != list(MODULES) or [r["declaration_count"] for r in manifest["catalog"]] != list(COUNTS):
        raise RuntimeError("frozen module catalog mismatch")
    before = []
    for entry in manifest["inputs"]:
        actual = sha(entry["path"])
        if actual != entry["sha256"]:
            raise RuntimeError("prepared input changed: " + entry["path"])
        before.append({"path": entry["path"], "sha256": actual})
    closure_path = Path(manifest["cache_closure_path"])
    closure = json.loads(closure_path.read_text(encoding="utf-8-sig"))
    cache_before = []
    for entry in closure["artifacts"]:
        actual = sha(entry["path"])
        if actual != entry["sha256"]:
            raise RuntimeError("readonly static cache import closure changed: " + entry["path"])
        cache_before.append({"path": entry["path"], "sha256": actual})
    libraries = [CACHE / package / ".lake" / "build" / "lib" for package in PACKAGES]
    if any(not path.is_dir() for path in libraries):
        raise RuntimeError("a cached LEAN_PATH directory is absent")
    out = ROLE / args.attempt
    out.mkdir(exist_ok=False)
    pre = out / "PREEXEC_FILES"
    pre.mkdir()
    for index, entry in enumerate(before):
        path = Path(entry["path"])
        (pre / (str(index).zfill(3) + "_" + path.name)).write_bytes(path.read_bytes())
    (pre / "ROOT_GATE.json").write_bytes(gate_path.read_bytes())
    (pre / "SOURCE_MANIFEST.json").write_bytes(manifest_path.read_bytes())
    env = dict(os.environ)
    lean_paths = [out, GAMMA_DIR] + libraries
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in lean_paths)
    write_new(out / "PREEXEC.json", {
        "time": now(), "inputs": before, "gate_path": str(gate_path), "gate_sha256": sha(gate_path),
        "source_manifest_sha256": sha(manifest_path), "python_sha256": sha(PYTHON), "lean_sha256": sha(LEAN),
        "lean_path": [str(path) for path in lean_paths], "numeric_evidence": numeric,
        "cache_artifacts_hash_only_readonly": cache_before,
    })
    write_new(out / "START.json", {
        "time": now(), "scope": "AUTHOR_H1_PSI_SOURCE_BATCH_ONLY", "attempt": args.attempt,
        "child_invocations_maximum": 4, "stop_first_failure": True, "hidden_retries": False,
    })
    rows = []
    failed = False
    for module, catalog in zip(MODULES, manifest["catalog"], strict=True):
        if failed:
            rows.append({"module": module, "status": "NOT_INVOKED_PREVIOUS_MODULE_FAILED"})
            continue
        source = ROLE / "source_final" / (module + ".lean")
        expected = catalog["declarations"]
        target = out / (module + ".olean")
        command = [str(LEAN), "-DmaxHeartbeats=1000000", "-o", str(target), str(source)]
        started = now()
        write_new(out / (module + "_START.json"), {"time": started, "command": command, "source_sha256": sha(source)})
        timed_out = False
        try:
            child = subprocess.run(command, cwd=str(source.parent), env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, check=False, timeout=180)
            raw, code = child.stdout, child.returncode
        except subprocess.TimeoutExpired as error:
            raw, code, timed_out = error.stdout or b"", 124, True
        log = out / (module + ".log")
        log.write_bytes(raw)
        axioms, coverage = audit_axioms(raw.decode("utf-8", errors="replace"), expected)
        ok = code == 0 and target.exists() and coverage
        row = {"module": module, "command": command, "cwd": str(source.parent), "started_at": started,
               "finished_at": now(), "exit_code": code, "timed_out": timed_out,
               "source_sha256": sha(source), "log_sha256": sha(log),
               "olean_sha256": sha(target) if target.exists() else None, "axiom_rows": axioms,
               "exact_axiom_coverage_standard_only": coverage, "status": "AUTHOR_LEAN_AUX_PASS" if ok else "AUTHOR_LEAN_FAIL"}
        rows.append(row)
        write_new(out / (module + "_FIN.json"), row)
        print(json.dumps(row, sort_keys=True), flush=True)
        failed = not ok
    after = [{"path": entry["path"], "sha256": sha(entry["path"])} for entry in before]
    cache_after = [{"path": entry["path"], "sha256": sha(entry["path"])} for entry in cache_before]
    unchanged = after == before and cache_after == cache_before
    write_new(out / "POSTEXEC.json", {"time": now(), "inputs": after, "all_inputs_unchanged": unchanged,
                                      "cache_artifacts_hash_only_readonly": cache_after})
    ok = unchanged and not failed and sum("exit_code" in row for row in rows) == 4
    write_new(out / "receipt.json", {
        "time": now(), "attempt": args.attempt, "stage": "H1_PSI_BATCH01", "rows": rows,
        "actual_child_invocations": sum("exit_code" in row for row in rows), "all_inputs_unchanged": unchanged,
        "status": "AUTHOR_PSI_BATCH_AUX_PASS" if ok else "AUTHOR_PSI_BATCH_FAILED",
        "stop_first_failure": True, "hidden_retries": False, "independent_judge_required": True,
        "P1_author_source_compiled": ok, "C5_paid": False, "global_H1_paid": False, "D_N_paid": False, "victory": False,
    })
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
