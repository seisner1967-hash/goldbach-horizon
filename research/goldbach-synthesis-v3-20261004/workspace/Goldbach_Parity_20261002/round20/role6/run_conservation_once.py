"""Explicit root-gated one-shot launcher for NEW byte-only preflight20."""
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
OWN = ROUND / "role6"
SOURCE = ROUND / "conservation.py"
LAUNCHER = OWN / "run_conservation_once.py"
PREPARATION = OWN / "preparation.json"
REGISTRY = ROUND / "previous_artifacts_sha256.json"
PROBE = ROUND / "PROBE_BLOCK.md"
CONTROLLER = BASE / "round19" / "controller_manifest.json"
INPUT_HASHES = BASE / "INPUT_HASHES.json"
EXPECTED_AUTH_PATH = BASE / ".arbor" / "sessions" / "parity" / ".coordinator" / "messages" / "round20_conservation_authorization.json"
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
EXPECTED_PYTHON = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
EXPECTED_REGISTRY = "9f238497b57a2dc7e46e26a67cb5e6a468be8f4e6a73525449a87406304a36b5"
EXPECTED_PROBE = "69df06d7abc3619ba51465b74912f6bf32a2f49f901d72533c4ba9945777685e"
EXPECTED_CONTROLLER = "299a605efaa7cf6721e3b65bfea8af976bcbfcdbb1bc841eee6f4a0d9d9d4d08"
AUTH_TOKEN = "ROOT20_CONSERVATION_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01"


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


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
    args = parser.parse_args()
    auth_path = Path(args.root_authorization)
    if auth_path.resolve(strict=True) != EXPECTED_AUTH_PATH.resolve(strict=True):
        raise RuntimeError("Unexpected root authorization file")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha256(PYTHON) != EXPECTED_PYTHON:
        raise RuntimeError("Unexpected Python executable or binary SHA")
    gate = json.loads(auth_path.read_text(encoding="utf-8"))
    if (gate.get("authorization") != AUTH_TOKEN or gate.get("root_authorized") is not True
            or gate.get("round") != 20 or gate.get("role") != 6
            or gate.get("all_preflight_sources_fully_read") is not True
            or gate.get("new_metadata_preflight_only") is not True
            or gate.get("attempt") != 1):
        raise RuntimeError("Missing concrete root authorization after FULL source inspection")
    source_digest = gate["source_sha256"]
    launcher_digest = gate["launcher_sha256"]
    preparation_digest = gate["preparation_sha256"]
    fixed = {
        SOURCE: source_digest, LAUNCHER: launcher_digest, PREPARATION: preparation_digest,
        REGISTRY: EXPECTED_REGISTRY, PROBE: EXPECTED_PROBE, CONTROLLER: EXPECTED_CONTROLLER,
        INPUT_HASHES: gate["original_hash_map_sha256"],
    }
    for path, expected in fixed.items():
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
        "preparation": (PREPARATION, OWN / f"{stem}_preparation.json"),
        "authorization": (auth_path, OWN / f"{stem}_authorization.json"),
        "registry": (REGISTRY, OWN / f"{stem}_registry.json"),
        "probe": (PROBE, OWN / f"{stem}_probe.md"),
        "controller19": (CONTROLLER, OWN / f"{stem}_controller19.json"),
        "original_hash_map": (INPUT_HASHES, OWN / f"{stem}_input_hashes.json"),
    }
    targets = [reserved, started, receipt, log, result] + [pair[1] for pair in captures.values()]
    if any(path.exists() for path in targets):
        raise RuntimeError("One-shot preflight target already exists; no routine rerun allowed")
    write_json_exclusive(reserved, {
        "reserved_at_utc": utc(), "root_authorization": str(auth_path),
        "authorization_token": AUTH_TOKEN,
        "round": 20, "role": 6, "attempt": 1, "subprocess_started": False,
    })
    auth_digest = sha256(auth_path)
    snapshots = {name: capture_exclusive(source, target) for name, (source, target) in captures.items()}
    expected_captures = {
        "source": source_digest, "launcher": launcher_digest,
        "preparation": preparation_digest, "authorization": auth_digest,
        "registry": EXPECTED_REGISTRY, "probe": EXPECTED_PROBE,
        "controller19": EXPECTED_CONTROLLER,
        "original_hash_map": gate["original_hash_map_sha256"],
    }
    for name, expected in expected_captures.items():
        if snapshots[name]["sha256"] != expected:
            raise RuntimeError(f"Input changed before PREEXEC capture: {name}")
    command = [str(PYTHON), "-B", "-X", "utf8", snapshots["source"]["snapshot"]]
    started_record = {
        "started_at_utc": utc(), "round": 20, "role": 6, "attempt": 1,
        "root_authorization": str(auth_path), "root_authorization_sha256": auth_digest,
        "authorization_token": AUTH_TOKEN,
        "launcher_command": [str(PYTHON), "-B", "-X", "utf8", str(LAUNCHER),
                             "--root-authorization", str(auth_path)],
        "subprocess_command": command, "cwd": str(ROUND),
        "python_executable": str(PYTHON), "python_sha256": EXPECTED_PYTHON,
        "captures_preexec": snapshots, "log": str(log), "result": str(result),
        "environment_changes": {"PYTHONDONTWRITEBYTECODE": "1", "PYTHONUTF8": "1"},
        "operation": "NEW_ROUND20_EXACT_BYTE_CONSERVATION_ONLY_BEFORE_AND_AFTER",
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
