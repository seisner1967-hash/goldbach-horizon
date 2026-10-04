"""Explicitly authorized one-shot launcher for the NEW byte-only preflight19."""
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
ROUND = BASE / "round19"
OWN = ROUND / "role6"
SOURCE = ROUND / "conservation.py"
LAUNCHER = OWN / "run_conservation_once.py"
REGISTRY = ROUND / "previous_artifacts_sha256.json"
PROBE = ROUND / "PROBE_BLOCK.md"
CONTROLLER = BASE / "round18" / "controller_manifest.json"
INPUT_HASHES = BASE / "INPUT_HASHES.json"
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
EXPECTED_REGISTRY = "8c0abf930ee8c47b64d335ed286af4566fc674b573216f82f12b05c4ec877150"
EXPECTED_PROBE = "5f9e429bc264002044da60139f3942e7c3de909116d41e6cc52f70afb9a5a12d"
EXPECTED_CONTROLLER = "ce00517b1df6f4fc89f27667be44dd7f2c4d3331c8022fd14e4c505392175c5c"


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def write_json_exclusive(path: Path, value: dict) -> None:
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def capture_exclusive(source: Path, target: Path) -> dict:
    data = source.read_bytes()
    with target.open("xb") as handle:
        handle.write(data)
    return {
        "original": str(source), "snapshot": str(target),
        "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-authorization", required=True)
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--launcher-sha256", required=True)
    args = parser.parse_args()
    if not args.root_authorization.strip():
        raise RuntimeError("A distinct explicit root authorization is required")
    if Path(sys.executable).resolve() != PYTHON.resolve():
        raise RuntimeError("Unexpected Python executable")
    for path, expected in ((SOURCE, args.source_sha256), (LAUNCHER, args.launcher_sha256),
                           (REGISTRY, EXPECTED_REGISTRY), (PROBE, EXPECTED_PROBE),
                           (CONTROLLER, EXPECTED_CONTROLLER)):
        if sha256(path) != expected:
            raise RuntimeError(f"Frozen preparation SHA mismatch: {path}")
    stem = "conservation_attempt01"
    reserved = OWN / f"{stem}_reserved.json"
    started = OWN / f"{stem}_started.json"
    receipt = OWN / f"{stem}_receipt.json"
    log = OWN / f"{stem}.log"
    result = ROUND / "conservation.json"
    captures = {
        "source": (SOURCE, OWN / f"{stem}_source.py.txt"),
        "launcher": (LAUNCHER, OWN / f"{stem}_launcher.py.txt"),
        "registry": (REGISTRY, OWN / f"{stem}_registry.json"),
        "probe": (PROBE, OWN / f"{stem}_probe.md"),
        "controller18": (CONTROLLER, OWN / f"{stem}_controller18.json"),
        "original_hash_map": (INPUT_HASHES, OWN / f"{stem}_input_hashes.json"),
    }
    targets = [reserved, started, receipt, log, result] + [pair[1] for pair in captures.values()]
    if any(path.exists() for path in targets):
        raise RuntimeError("One-shot preflight target already exists; no routine rerun allowed")
    write_json_exclusive(reserved, {
        "reserved_at_utc": utc(), "root_authorization": args.root_authorization,
        "round": 19, "role": 6, "attempt": 1, "subprocess_started": False,
    })
    snapshots = {name: capture_exclusive(source, target) for name, (source, target) in captures.items()}
    capture_expected = {
        "source": args.source_sha256, "launcher": args.launcher_sha256,
        "registry": EXPECTED_REGISTRY, "probe": EXPECTED_PROBE,
        "controller18": EXPECTED_CONTROLLER,
    }
    for name, expected in capture_expected.items():
        if snapshots[name]["sha256"] != expected:
            raise RuntimeError(f"Preparation input changed before PREEXEC capture: {name}")
    command = [str(PYTHON), "-B", "-X", "utf8", snapshots["source"]["snapshot"]]
    started_record = {
        "started_at_utc": utc(), "round": 19, "role": 6, "attempt": 1,
        "root_authorization": args.root_authorization,
        "launcher_command": [str(PYTHON), "-B", "-X", "utf8", str(LAUNCHER),
                             "--root-authorization", args.root_authorization,
                             "--source-sha256", args.source_sha256,
                             "--launcher-sha256", args.launcher_sha256],
        "subprocess_command": command, "cwd": str(ROUND),
        "python_executable": str(PYTHON), "python_sha256": sha256(PYTHON),
        "captures_preexec": snapshots, "log": str(log), "result": str(result),
        "environment_changes": {"PYTHONDONTWRITEBYTECODE": "1", "PYTHONUTF8": "1"},
        "operation": "NEW_ROUND19_EXACT_BYTE_CONSERVATION_ONLY",
        "mathematical_execution": False,
    }
    write_json_exclusive(started, started_record)
    environment = os.environ.copy()
    environment.update(started_record["environment_changes"])
    launch_error = None
    exit_code = None
    with log.open("xb") as handle:
        try:
            completed = subprocess.run(command, cwd=ROUND, env=environment,
                                       stdout=handle, stderr=subprocess.STDOUT, check=False)
            exit_code = completed.returncode
        except OSError as error:
            launch_error = {"type": type(error).__name__, "message": str(error)}
            handle.write((repr(error) + "\n").encode("utf-8"))
    final = {
        **started_record, "finished_at_utc": utc(), "exit_code": exit_code,
        "subprocess_launch_error": launch_error,
        "started_receipt_sha256": sha256(started), "log_sha256": sha256(log),
        "result_sha256": sha256(result) if result.is_file() else None,
        "subprocess_finished": launch_error is None,
        "root_authorized_new_preflight_only": True,
        "old_preflights_or_mathematics_executed": False,
        "victory": False,
    }
    write_json_exclusive(receipt, final)
    print(json.dumps({
        "receipt": str(receipt), "receipt_sha256": sha256(receipt),
        "exit_code": exit_code, "launch_error": launch_error,
        "log_sha256": final["log_sha256"], "result_sha256": final["result_sha256"],
    }, indent=2, sort_keys=True))
    if launch_error is not None:
        return 2
    return int(exit_code)


if __name__ == "__main__":
    raise SystemExit(main())
