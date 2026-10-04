"""Compile one frozen author stage only after its own root gate.

Each module is invoked once in a stage; no hidden retry or cache PASS reuse.
This launcher has not been executed during source preparation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from datetime import datetime, timezone

ROLE = Path(__file__).resolve().parent
BASE = ROLE.parents[2]
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
CANONICAL_CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
STAGE01_MODULES = ("EpsteinFinite22",)
DEPENDENCY_DIR = ROLE.parents[1] / "revision02" / "stage01_attempt02"
DEPENDENCY_OLEAN_SHA = "9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d"


def sha(path):
    with Path(path).open("rb") as f:
        h = hashlib.sha256()
        for block in iter(lambda: f.read(1048576), b""):
            h.update(block)
        return h.hexdigest()


def write_exclusive(path, data):
    with Path(path).open("x", encoding="utf-8", newline="\n") as f:
        json.dump(data, f, ensure_ascii=False, indent=2, sort_keys=True)
        f.write("\n")


def now():
    return datetime.now(timezone.utc).isoformat()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gate", required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if args.attempt != "stage02_attempt03":
        raise RuntimeError("this frozen launcher authorizes only its single named attempt")
    manifest_path = ROLE / "source_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    gate_path = Path(args.gate).resolve()
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    required_gate = {
        "role": "ROLE3", "node_id": "16.1",
        "attempt": args.attempt, "stage": "G0_FINITE_REVISION03",
        "authorized": True, "numeric_verdict": "EPSTEIN_UNFOLDING_AUX_PASS",
        "source_manifest_sha256": sha(manifest_path),
        "launcher_sha256": sha(Path(__file__)),
        "python_sha256": PYTHON_SHA, "lean_sha256": LEAN_SHA,
        "modules": list(STAGE01_MODULES), "no_win": True,
        "dependency_olean_sha256": DEPENDENCY_OLEAN_SHA,
    }
    for key, value in required_gate.items():
        if gate.get(key) != value:
            raise RuntimeError("root gate mismatch: " + key)
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA:
        raise RuntimeError("Python runtime binding mismatch")
    if sha(LEAN) != LEAN_SHA:
        raise RuntimeError("Lean runtime binding mismatch")
    if manifest["modules"] != list(STAGE01_MODULES):
        raise RuntimeError("module catalog mismatch")
    if sha(DEPENDENCY_DIR / "EpsteinKernel22.olean") != DEPENDENCY_OLEAN_SHA:
        raise RuntimeError("immutable Kernel dependency changed")
    before = []
    for entry in manifest["inputs"]:
        actual = sha(entry["path"])
        if actual != entry["sha256"]:
            raise RuntimeError("source input changed: " + entry["path"])
        before.append({"path": entry["path"], "sha256": actual})
    out = ROLE / args.attempt
    out.mkdir(exist_ok=False)
    captures = out / "PREEXEC"
    captures.mkdir()
    for index, entry in enumerate(before):
        src = Path(entry["path"])
        (captures / (str(index).zfill(3) + "_" + src.name)).write_bytes(src.read_bytes())
    write_exclusive(out / "PREEXEC.json", {
        "time": now(), "inputs": before,
        "gate_path": str(gate_path), "gate_sha256": sha(gate_path),
        "manifest_sha256": sha(manifest_path),
        "python_sha256": sha(PYTHON), "lean_sha256": sha(LEAN),
        "mathlib_commit": "9837ca9d65d9de6fad1ef4381750ca688774e608",
    })
    env = dict(os.environ)
    paths = [out, DEPENDENCY_DIR] + [CANONICAL_CACHE / package / ".lake" / "build" / "lib" for package in PACKAGES]
    if any(not path.is_dir() for path in paths):
        raise RuntimeError("missing cached library path")
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in paths)
    write_exclusive(out / "START.json", {
        "time": now(), "scope": "AUTHOR_G0_FINITE_REVISION03_ONLY",
        "attempt": args.attempt, "gate_sha256": sha(gate_path),
        "child_invocations_maximum": 1, "hidden_retries": False,
    })
    rows = []
    for module in STAGE01_MODULES:
        if rows and rows[-1]["exit_code"] != 0:
            rows.append({"module": module, "status": "NOT_INVOKED_DEPENDENCY_FAILED"})
            break
        source = ROLE / (module + ".lean")
        target = out / (module + ".olean")
        command = [str(LEAN), "-o", str(target), str(source)]
        started = now()
        completed = subprocess.run(command, cwd=str(ROLE), env=env,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   check=False)
        log = out / (module + ".log")
        log.write_bytes(completed.stdout)
        row = {"module": module, "command": command, "cwd": str(ROLE),
               "source_sha256": sha(source), "started_at": started,
               "finished_at": now(), "exit_code": completed.returncode,
               "log_sha256": sha(log),
               "olean_sha256": sha(target) if target.exists() else None,
               "status": "LEAN_PASS_AUX" if completed.returncode == 0 else "LEAN_FAIL"}
        rows.append(row)
        print(json.dumps(row, sort_keys=True), flush=True)
    post = [{"path": entry["path"], "sha256": sha(entry["path"])} for entry in before]
    unchanged = post == before
    write_exclusive(out / "POSTEXEC.json", {"time": now(), "inputs": post, "unchanged": unchanged})
    ok = unchanged and len(rows) == 1 and all(row.get("exit_code") == 0 for row in rows)
    write_exclusive(out / "receipt.json", {
        "time": now(), "stage": "G0_FINITE_REVISION03", "attempt": args.attempt,
        "actual_child_invocations": sum("exit_code" in row for row in rows),
        "rows": rows, "all_source_inputs_unchanged": unchanged,
        "status": "AUTHOR_STAGE_AUX_PASS" if ok else "AUTHOR_STAGE_FAILED",
        "infinite_unfolding_complete": False, "D_N_bound": False, "victory": False,
    })
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
