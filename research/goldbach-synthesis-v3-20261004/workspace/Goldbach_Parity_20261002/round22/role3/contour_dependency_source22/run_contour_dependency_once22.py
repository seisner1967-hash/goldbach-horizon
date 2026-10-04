"""SOURCE ONLY: new Box12 -> corrected Contour11, two children maximum.

No mathematical Python calculation or numerical bank. A separate actual ROOT
gate is required. Independently judged Gamma and Gamma-prime are readonly.
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
BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
MODULES = ("GammaBoxBounds22", "GammaContourComponent22")
COUNTS = (12, 11)
GAMMA_DIR = BASE / "round22" / "judge5" / "batch02_attempt01"
GAMMA_SHA = "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477"
DERIVATIVE_DIR = BASE / "round22" / "judge5" / "batch03" / "batch03_attempt01"
DERIVATIVE_SHA = "0618f801c5feec7b760ba18ab3dddc960519b398dd1d1b719acc809132518125"
REGISTRY = BASE / "round22" / "previous_artifacts_sha256.json"
REGISTRY_SHA = "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99"
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


def verify(items):
    rows = []
    for item in items:
        path = Path(item["path"])
        actual = sha(path)
        if actual != item["sha256"]:
            raise RuntimeError("readonly input changed: " + str(path))
        rows.append({"path": str(path), "sha256": actual})
    return rows


def archives():
    if sha(REGISTRY) != REGISTRY_SHA:
        raise RuntimeError("protected archive registry changed")
    registry = json.loads(REGISTRY.read_text(encoding="utf-8-sig"))
    if registry["file_count"] != 3089 or len(registry["sha256"]) != 3089:
        raise RuntimeError("protected archive count changed")
    items = []
    for label, expected in registry["sha256"].items():
        path = (BASE / label).resolve()
        if BASE.resolve() not in path.parents:
            raise RuntimeError("protected archive path escaped workspace")
        items.append({"path": str(path), "sha256": expected})
    return verify(items)


def audit_axioms(log, expected):
    rows = []
    pattern = r"^'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)[ \t\r]*$"
    for hit in re.finditer(pattern, log, re.MULTILINE):
        names = [] if hit[2] is None else [s.strip() for s in hit[2].split(",") if s.strip()]
        rows.append({"declaration": hit[1], "axioms": names})
    names = [row["declaration"] for row in rows]
    heads = re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)", log, re.MULTILINE)
    ok = (names == expected and heads == names and len(set(names)) == len(names)
          and all(set(row["axioms"]) <= ALLOWED_AXIOMS for row in rows)
          and "sorryAx" not in log)
    return rows, ok


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gate", required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if args.attempt != "contour_dependency_attempt01":
        raise RuntimeError("only the separately prepared first microbatch is implemented")
    manifest_path = ROLE / "prepared_manifest22.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    gate_path = Path(args.gate).resolve()
    if gate_path.parent != (BASE / ".arbor" / "sessions" / "parity" / ".coordinator" / "messages").resolve():
        raise RuntimeError("gate must be an actual ROOT-owned coordinator/messages file")
    gate = json.loads(gate_path.read_text(encoding="utf-8-sig"))
    requirements = {
        "role": "ROLE3", "node_id": "15.3", "stage": "H1_CONTOUR_DEPENDENCY_MICROBATCH01",
        "attempt": args.attempt, "authorized": True, "modules": list(MODULES),
        "source_manifest_sha256": sha(manifest_path), "launcher_sha256": sha(Path(__file__)),
        "python_sha256": PYTHON_SHA, "lean_sha256": LEAN_SHA,
        "readonly_gamma_olean_sha256": GAMMA_SHA,
        "readonly_gamma_derivative_olean_sha256": DERIVATIVE_SHA,
        "numeric_pass_required": False, "compiler_invocations_maximum": 2,
        "stop_first_failure": True, "retry_count": 0, "no_win": True,
    }
    for key, value in requirements.items():
        if gate.get(key) != value:
            raise RuntimeError("ROOT gate mismatch: " + key)
    if (Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA
            or sha(LEAN) != LEAN_SHA or not sys.flags.dont_write_bytecode or sys.flags.utf8_mode != 1):
        raise RuntimeError("canonical runtime binding mismatch")
    if sha(GAMMA_DIR / "GammaPrerequisites22.olean") != GAMMA_SHA:
        raise RuntimeError("readonly independently judged Gamma changed")
    if sha(DERIVATIVE_DIR / "GammaDerivative22.olean") != DERIVATIVE_SHA:
        raise RuntimeError("readonly independently judged Gamma derivative changed")
    if manifest["modules"] != list(MODULES) or [r["declaration_count"] for r in manifest["catalog"]] != list(COUNTS):
        raise RuntimeError("frozen module catalogue mismatch")
    before = verify(manifest["inputs"])
    closure = json.loads(Path(manifest["cache_closure_path"]).read_text(encoding="utf-8-sig"))
    if closure["unresolved_modules"] != [] or not closure["implicit_Init_and_Prelude_bound"]:
        raise RuntimeError("static import closure is incomplete")
    cache_before = verify(closure["artifacts"])
    archive_before = archives()
    libraries = [CACHE / package / ".lake" / "build" / "lib" for package in PACKAGES]
    if any(not path.is_dir() for path in libraries):
        raise RuntimeError("a cached LEAN_PATH directory is absent")
    out = ROLE / args.attempt
    out.mkdir(exist_ok=False)
    pre = out / "PREEXEC_FILES"
    pre.mkdir()
    captures = []
    for index, entry in enumerate(before):
        path = Path(entry["path"])
        captured = pre / (str(index).zfill(3) + "_" + path.name)
        captured.write_bytes(path.read_bytes())
        if sha(captured) != entry["sha256"]:
            raise RuntimeError("PREEXEC capture changed")
        captures.append({"original": str(path), "captured": str(captured), "sha256": sha(captured)})
    for name, path in (("ROOT_GATE.json", gate_path), ("SOURCE_MANIFEST.json", manifest_path)):
        captured = pre / name
        captured.write_bytes(path.read_bytes())
        if sha(captured) != sha(path):
            raise RuntimeError("PREEXEC gate/manifest capture changed")
        captures.append({"original": str(path), "captured": str(captured), "sha256": sha(captured)})
    env = dict(os.environ)
    lean_paths = [out, DERIVATIVE_DIR, GAMMA_DIR] + libraries
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in lean_paths)
    write_new(out / "PREEXEC.json", {
        "time": now(), "inputs": before, "gate_path": str(gate_path), "gate_sha256": sha(gate_path),
        "source_manifest_sha256": sha(manifest_path), "python_sha256": sha(PYTHON), "lean_sha256": sha(LEAN),
        "lean_path": [str(path) for path in lean_paths], "captures": captures,
        "cache_artifacts_hash_only_readonly": cache_before, "protected_archives_hash_only": archive_before,
    })
    write_new(out / "START.json", {
        "time": now(), "scope": "NEW_AUTHOR_BOX_CONTOUR_MICROBATCH_ONLY", "attempt": args.attempt,
        "child_invocations_maximum": 2, "stop_first_failure": True, "hidden_retries": False,
    })
    rows, failed = [], False
    for module, catalog in zip(MODULES, manifest["catalog"], strict=True):
        if failed:
            rows.append({"module": module, "status": "NOT_INVOKED_PREVIOUS_MODULE_FAILED"})
            continue
        source = ROLE / "source_final" / (module + ".lean")
        target = out / (module + ".olean")
        command = [str(LEAN), "-DmaxHeartbeats=1000000", "-o", str(target), str(source)]
        started = now()
        write_new(out / (module + "_START.json"), {"time": started, "command": command, "source_sha256": sha(source)})
        timed_out, launch_error = False, None
        try:
            child = subprocess.run(command, cwd=str(source.parent), env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, check=False, timeout=180)
            raw, code = child.stdout, child.returncode
        except subprocess.TimeoutExpired as error:
            raw, code, timed_out = error.stdout or b"", 124, True
        except OSError as error:
            raw, code, launch_error = str(error).encode("utf-8"), 127, str(error)
        log = out / (module + ".log")
        log.write_bytes(raw)
        axioms, coverage = audit_axioms(raw.decode("utf-8", errors="replace"), catalog["declarations"])
        ok = code == 0 and target.exists() and coverage
        row = {"module": module, "command": command, "cwd": str(source.parent), "started_at": started,
               "finished_at": now(), "exit_code": code, "timed_out": timed_out, "launch_error": launch_error,
               "source_sha256": sha(source), "log_sha256": sha(log),
               "olean_sha256": sha(target) if target.exists() else None, "axiom_rows": axioms,
               "exact_axiom_coverage_standard_only": coverage,
               "status": "AUTHOR_LEAN_AUX_PASS" if ok else "AUTHOR_LEAN_FAIL"}
        rows.append(row)
        write_new(out / (module + "_FIN.json"), row)
        print(json.dumps(row, sort_keys=True), flush=True)
        failed = not ok
    after = verify(manifest["inputs"])
    cache_after = verify(closure["artifacts"])
    archive_after = archives()
    captured_after = verify([{"path": row["captured"], "sha256": row["sha256"]} for row in captures])
    unchanged = after == before and cache_after == cache_before and archive_after == archive_before
    write_new(out / "POSTEXEC.json", {
        "time": now(), "inputs": after, "all_inputs_unchanged": unchanged,
        "cache_artifacts_hash_only_readonly": cache_after, "protected_archives_hash_only": archive_after,
        "capture_hashes": captured_after,
    })
    invoked = sum("exit_code" in row for row in rows)
    ok = unchanged and not failed and invoked == 2
    write_new(out / "receipt.json", {
        "time": now(), "attempt": args.attempt, "stage": "H1_CONTOUR_DEPENDENCY_MICROBATCH01", "rows": rows,
        "actual_child_invocations": invoked, "all_inputs_unchanged": unchanged, "protected_archives_verified": 3089,
        "status": "AUTHOR_CONTOUR_DEPENDENCY_AUX_PASS" if ok else "AUTHOR_CONTOUR_DEPENDENCY_FAILED",
        "stop_first_failure": True, "hidden_retries": False, "independent_judge_required": True,
        "old_batch_replayed": False, "readonly_judged_dependencies_recompiled": False,
        "C5_paid": False, "global_H1_paid": False, "D_N_paid": False, "victory": False,
    })
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
