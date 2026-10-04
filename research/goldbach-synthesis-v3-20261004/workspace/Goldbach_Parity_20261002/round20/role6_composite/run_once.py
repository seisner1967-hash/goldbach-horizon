"""NEW composite20 one-shot launch; PREEXEC captures, concrete root gate, no retries."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
ROUND = BASE / "round20"
OWN = ROUND / "role6_composite"
LAUNCHER = OWN / "run_once.py"
PREPARATION = OWN / "preparation.json"
AUTH_PATH = BASE / ".arbor" / "sessions" / "parity" / ".coordinator" / "messages" / "round20_composite_authorization.json"
AUTH_TOKEN = "ROOT20_COMPOSITE_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01"
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
SOURCES = {name: OWN / name for name in ("composite_checks.py", "bank.py", "ap.py", "reference.py",
                                       "storage.py", "integral.py", "certify.py", "arithmetic.py", "outward.py")}


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def exclusive_json(path, value):
    with path.open("x", encoding="utf8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def capture(source, snapshot):
    data = source.read_bytes()
    with snapshot.open("xb") as handle:
        handle.write(data)
    return {"original": str(source), "snapshot": str(snapshot), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-authorization", required=True)
    args = parser.parse_args()
    auth_path = Path(args.root_authorization)
    if auth_path.resolve(strict=True) != AUTH_PATH.resolve(strict=True):
        raise RuntimeError("Unexpected composite authorization path")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha256(PYTHON) != PYTHON_SHA:
        raise RuntimeError("Unexpected Python runtime or executable SHA")
    gate = json.loads(auth_path.read_text(encoding="utf8"))
    if (gate.get("authorization") != AUTH_TOKEN or gate.get("root_authorized") is not True
            or gate.get("round") != 20 or gate.get("role") != 6 or gate.get("node") != "13.12"
            or gate.get("attempt") != 1 or gate.get("all_sources_fully_read") is not True
            or gate.get("canonical_new_numerical_execution_authorized") is not True
            or gate.get("new_bank_only") != "COMPOSITE20_13.12"):
        raise RuntimeError("Missing concrete root authorization after FULL source review")
    if sha256(PREPARATION) != gate["preparation_sha256"]:
        raise RuntimeError("Frozen preparation SHA mismatch")
    preparation = json.loads(PREPARATION.read_text(encoding="utf8"))
    expected_codes = preparation["code_sha256"]
    if expected_codes != gate["code_sha256"]:
        raise RuntimeError("Root code map differs from prepared code map")
    expected = {path: expected_codes[name] for name, path in SOURCES.items()}
    expected[LAUNCHER] = expected_codes["run_once.py"]
    expected[PREPARATION] = gate["preparation_sha256"]
    expected[auth_path] = sha256(auth_path)
    for path, digest in preparation["frozen_input_sha256"].items():
        expected[Path(path)] = digest
    for path, digest in expected.items():
        if sha256(path) != digest:
            raise RuntimeError(f"PREEXEC frozen input mismatch: {path}")
    out = OWN / "canonical_attempt01"
    result = ROUND / "composite.json"
    reserved = OWN / "canonical_attempt01_reserved.json"
    if out.exists() or result.exists() or reserved.exists():
        raise RuntimeError("Canonical composite attempt already reserved or executed; no PASS replay")
    exclusive_json(reserved, {"reserved_at_utc": utc(), "round": 20, "role": 6, "node": "13.12",
                              "attempt": 1, "authorization": AUTH_TOKEN, "subprocess_started": False})
    out.mkdir()
    inputs = out / "inputs"
    inputs.mkdir()
    captures = {}
    for name, path in SOURCES.items():
        captures["code:" + name] = capture(path, inputs / name)
    captures["launcher"] = capture(LAUNCHER, inputs / "launcher.py.txt")
    captures["preparation"] = capture(PREPARATION, inputs / "preparation.json")
    captures["authorization"] = capture(auth_path, inputs / "authorization.json")
    for index, (path, digest) in enumerate(preparation["frozen_input_sha256"].items()):
        original = Path(path)
        captures["input:" + path] = capture(original, inputs / (f"data_{index:02d}_" + original.name))
    for record in captures.values():
        if record["sha256"] != expected[Path(record["original"])]:
            raise RuntimeError("Input changed during PREEXEC snapshot capture")
    manifest = out / "input_manifest.json"
    exclusive_json(manifest, {"phase": "PREEXEC", "round": 20, "node": "13.12",
                              "all_captures_before_child_start": True, "bindings": captures})
    command = [str(PYTHON), "-B", "-X", "utf8", str(inputs / "composite_checks.py")]
    launcher_command = [str(PYTHON), "-B", "-X", "utf8", str(LAUNCHER),
                        "--root-authorization", str(auth_path)]
    started_path = out / "started.json"
    receipt_path = out / "receipt.json"
    log_path = out / "execution.log"
    started = {"started_at_utc": utc(), "round": 20, "role": 6, "node": "13.12", "attempt": 1,
               "authorization": AUTH_TOKEN, "root_authorization_path": str(auth_path),
               "root_authorization_sha256": sha256(auth_path), "launcher_command": launcher_command,
               "subprocess_command": command, "cwd": str(out), "runtime": str(PYTHON),
               "runtime_sha256": PYTHON_SHA, "input_manifest_path": str(manifest),
               "input_manifest_sha256": sha256(manifest), "captures_preexec": captures,
               "log_path": str(log_path), "result_path": str(result),
               "environment_changes": {"PYTHONDONTWRITEBYTECODE": "1", "PYTHONUTF8": "1",
                                       "PYTHONNOUSERSITE": "1", "PYTHONPATH": str(inputs)},
               "operation": "UNIQUE_NEW_FULL_COMPOSITE20_NUMERICAL_BANK_NO_OLD_IMPORT_OR_PRODUCER",
               "old_producer_or_Lean_executions": 0, "victory": False}
    exclusive_json(started_path, started)
    environment = os.environ.copy()
    environment.update(started["environment_changes"])
    exit_code, launch_error = None, None
    with log_path.open("xb") as handle:
        try:
            completed = subprocess.run(command, cwd=out, env=environment,
                                       stdout=handle, stderr=subprocess.STDOUT, check=False)
            exit_code = completed.returncode
        except OSError as error:
            launch_error = {"type": type(error).__name__, "message": str(error)}
            handle.write((repr(error) + "\n").encode("utf8"))
    changed_inputs = [{"path": str(path), "expected": digest, "actual": sha256(path)}
                      for path, digest in expected.items() if sha256(path) != digest]
    runtime_after = sha256(PYTHON)
    receipt = {**started, "finished_at_utc": utc(), "exit_code": exit_code, "launch_error": launch_error,
               "started_sha256": sha256(started_path), "log_sha256": sha256(log_path),
               "result_sha256": sha256(result) if result.is_file() else None,
               "frozen_input_changes_after": changed_inputs, "runtime_sha256_after": runtime_after,
               "canonical_subprocess_count": 1, "routine_replays": 0,
               "after_preservation_pass": not changed_inputs and runtime_after == PYTHON_SHA, "victory": False}
    exclusive_json(receipt_path, receipt)
    print(json.dumps({"receipt": str(receipt_path), "receipt_sha256": sha256(receipt_path),
                      "exit_code": exit_code, "launch_error": launch_error,
                      "log_sha256": receipt["log_sha256"], "result_sha256": receipt["result_sha256"],
                      "after_preservation_pass": receipt["after_preservation_pass"]}, sort_keys=True, indent=2))
    if launch_error is not None:
        return 2
    if changed_inputs or runtime_after != PYTHON_SHA:
        return 3
    return int(exit_code)


if __name__ == "__main__":
    raise SystemExit(main())
