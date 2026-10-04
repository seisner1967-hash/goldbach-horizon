"""Root-gated one-shot launcher for the NEW round21 metadata-only preflight."""
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
ROUND = BASE / "round21"
OWN = ROUND / "role6"
SOURCE = ROUND / "conservation.py"
LAUNCHER = OWN / "run_conservation_once.py"
PREPARATION = OWN / "preparation.json"
REGISTRY = ROUND / "previous_artifacts_sha256.json"
PROBE = ROUND / "PROBE_BLOCK.md"
CONTROLLER = BASE / "round20" / "controller_manifest.json"
INPUT_HASHES = BASE / "INPUT_HASHES.json"
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
REGISTRY_SHA = "5c1c372a2a723a1a06224c6531c2e0775978bbe902f02cf910450a583772896c"
PROBE_SHA = "015cccf57d59c53abd34f4b6623b891199fdb61a9f8acafcd4f352df0b8fd7de"
CONTROLLER_SHA = "815d2ce77851a01d9addfa4202a17edb787a42f7f080d4e41cab18aa7b002b04"
INPUT_HASHES_SHA = "5f3f8498fc1343b69ade24634d0253ec662c090641a852465e6b70059b005460"
AUTH_PATH = BASE / ".arbor" / "sessions" / "parity" / ".coordinator" / "messages" / "round21_conservation_authorization.json"
TOKEN = "ROOT21_CONSERVATION_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01"
ORIGINALS = {
    Path(r"D:\Users\Utilisateur\Downloads\goldbach_synthesis.pdf"):
        "bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24",
    Path(r"D:\Users\Utilisateur\Downloads\Goldbach_Continuation_Cofacteur_Court_2026-10-01.zip"):
        "32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd",
}


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def exclusive_json(path: Path, value: dict) -> None:
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def capture(source: Path, target: Path) -> dict:
    data = source.read_bytes()
    with target.open("xb") as handle:
        handle.write(data)
    return {"original": str(source), "snapshot": str(target),
            "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def post_observation(expected: dict[Path, str]) -> dict:
    observed = {}
    changed = []
    for path, wanted in expected.items():
        try:
            actual = digest(path) if path.is_file() else None
        except OSError as caught:
            actual = f"HASH_READ_ERROR:{type(caught).__name__}:{caught}"
        observed[str(path)] = actual
        if actual != wanted:
            changed.append({"path": str(path), "expected": wanted, "actual": actual})
    return {"checked_path_count": len(expected), "observed_sha256": observed,
            "changed": changed, "unchanged": not changed}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-authorization", required=True)
    args = parser.parse_args()
    authorization = Path(args.root_authorization)
    if authorization.resolve(strict=True) != AUTH_PATH.resolve(strict=True):
        raise RuntimeError("Unexpected root authorization path")
    if Path(sys.executable).resolve() != PYTHON.resolve() or digest(PYTHON) != PYTHON_SHA:
        raise RuntimeError("Known Python runtime path/SHA mismatch")
    gate = json.loads(authorization.read_text(encoding="utf-8"))
    required = {
        "authorization": TOKEN, "root_authorized": True, "round": 21, "role": 6,
        "attempt": 1, "all_preflight_sources_fully_read": True,
        "new_metadata_preflight_only": True,
        "registry_sha256": REGISTRY_SHA, "probe_sha256": PROBE_SHA,
        "controller20_sha256": CONTROLLER_SHA, "original_hash_map_sha256": INPUT_HASHES_SHA,
    }
    if any(gate.get(name) != value for name, value in required.items()):
        raise RuntimeError("Distinct root gate missing required FULL-read metadata-only fields")
    fixed = {
        SOURCE: gate["source_sha256"], LAUNCHER: gate["launcher_sha256"],
        PREPARATION: gate["preparation_sha256"], REGISTRY: REGISTRY_SHA,
        PROBE: PROBE_SHA, CONTROLLER: CONTROLLER_SHA, INPUT_HASHES: INPUT_HASHES_SHA,
        PYTHON: PYTHON_SHA, authorization: digest(authorization), **ORIGINALS,
    }
    for path, expected in fixed.items():
        if digest(path) != expected:
            raise RuntimeError(f"Prepared input byte identity mismatch: {path}")
    stem = "conservation_attempt01"
    reserved = OWN / f"{stem}_reserved.json"
    started = OWN / f"{stem}_started.json"
    receipt = OWN / f"{stem}_receipt.json"
    post_path = OWN / f"{stem}_post_integrity.json"
    runtime_path = OWN / f"{stem}_runtime_PREEXEC.json"
    originals_path = OWN / f"{stem}_originals_PREEXEC.json"
    log = OWN / f"{stem}.log"
    result = ROUND / "conservation.json"
    capture_plan = {
        "source": (SOURCE, OWN / f"{stem}_source_PREEXEC.py.txt"),
        "launcher": (LAUNCHER, OWN / f"{stem}_launcher_PREEXEC.py.txt"),
        "preparation": (PREPARATION, OWN / f"{stem}_preparation_PREEXEC.json"),
        "authorization": (authorization, OWN / f"{stem}_authorization_PREEXEC.json"),
        "registry": (REGISTRY, OWN / f"{stem}_registry_PREEXEC.json"),
        "probe": (PROBE, OWN / f"{stem}_probe_PREEXEC.md"),
        "controller20": (CONTROLLER, OWN / f"{stem}_controller20_PREEXEC.json"),
        "original_hash_map": (INPUT_HASHES, OWN / f"{stem}_input_hashes_PREEXEC.json"),
    }
    targets = [reserved, started, receipt, post_path, runtime_path, originals_path, log, result]
    targets += [target for _, target in capture_plan.values()]
    if any(path.exists() for path in targets):
        raise RuntimeError("Unique attempt01 target exists; no replay or target replacement")
    exclusive_json(reserved, {"reserved_at_utc": utc(), "round": 21, "role": 6,
                             "attempt": 1, "subprocess_started": False,
                             "authorization": str(authorization), "authorization_token": TOKEN})
    reserved_sha = digest(reserved)
    snapshots = {name: capture(source, target)
                 for name, (source, target) in capture_plan.items()}
    for name, entry in snapshots.items():
        if entry["sha256"] != fixed[Path(entry["original"])]:
            raise RuntimeError(f"Prepared input changed at PREEXEC capture: {name}")
    runtime_preexec = {"path": str(PYTHON), "sha256": digest(PYTHON),
                       "bytes": PYTHON.stat().st_size, "executed_version_probe": False,
                       "binary_copied": False}
    originals_preexec = {str(path): {"sha256": digest(path), "bytes": path.stat().st_size,
                                   "content_parsed": False, "copied": False}
                        for path in ORIGINALS}
    if runtime_preexec["sha256"] != PYTHON_SHA:
        raise RuntimeError("Runtime changed before START")
    for path, expected in ORIGINALS.items():
        if originals_preexec[str(path)]["sha256"] != expected:
            raise RuntimeError(f"Original input changed before START: {path}")
    exclusive_json(runtime_path, runtime_preexec)
    exclusive_json(originals_path, originals_preexec)
    runtime_receipt_sha = digest(runtime_path)
    originals_receipt_sha = digest(originals_path)
    command = [str(PYTHON), "-B", "-X", "utf8", snapshots["source"]["snapshot"]]
    started_record = {
        "started_at_utc": utc(), "round": 21, "role": 6, "attempt": 1,
        "operation": "NEW_ROUND21_EXACT_METADATA_BYTE_CONSERVATION_BEFORE_AND_AFTER",
        "authorization": str(authorization), "authorization_sha256": fixed[authorization],
        "authorization_token": TOKEN, "subprocess_command": command,
        "launcher_command": [str(PYTHON), "-B", "-X", "utf8", str(LAUNCHER),
                             "--root-authorization", str(authorization)],
        "cwd": str(ROUND), "captures_preexec": snapshots,
        "runtime_preexec_receipt": str(runtime_path),
        "runtime_preexec_receipt_sha256": runtime_receipt_sha,
        "originals_preexec_receipt": str(originals_path),
        "originals_preexec_receipt_sha256": originals_receipt_sha,
        "runtime": runtime_preexec, "originals": originals_preexec,
        "environment_changes": {"PYTHONDONTWRITEBYTECODE": "1", "PYTHONUTF8": "1"},
        "log": str(log), "result": str(result), "mathematical_execution": False,
        "old_producer_or_Lean_or_PDF_execution": False,
    }
    exclusive_json(started, started_record)
    started_sha = digest(started)
    environment = os.environ.copy()
    environment.update(started_record["environment_changes"])
    error = None
    exit_code = None
    with log.open("xb") as handle:
        try:
            completed = subprocess.run(command, cwd=ROUND, env=environment,
                                       stdout=handle, stderr=subprocess.STDOUT, check=False)
            exit_code = completed.returncode
        except OSError as caught:
            error = {"type": type(caught).__name__, "message": str(caught)}
            handle.write((repr(caught) + "\n").encode("utf-8"))
    finished_at = utc()
    post_expected = dict(fixed)
    post_expected.update({Path(entry["snapshot"]): entry["sha256"]
                          for entry in snapshots.values()})
    post_expected.update({runtime_path: runtime_receipt_sha, originals_path: originals_receipt_sha,
                          started: started_sha, reserved: reserved_sha})
    post = post_observation(post_expected)
    post.update({"observed_at_utc": utc(), "metadata_only": True})
    exclusive_json(post_path, post)
    result_status = None
    result_parse_error = None
    if result.is_file():
        try:
            result_status = json.loads(result.read_text(encoding="utf-8"))["status"]
        except (OSError, ValueError, KeyError, TypeError) as caught:
            result_parse_error = {"type": type(caught).__name__, "message": str(caught)}
    credited = (error is None and exit_code == 0 and post["unchanged"]
                and result_status == "PASS_EXACT_CONSERVATION")
    final = {
        **started_record, "finished_at_utc": finished_at, "exit_code": exit_code,
        "launch_error": error, "subprocess_finished": error is None,
        "started_receipt_sha256": started_sha, "log_sha256": digest(log),
        "result_sha256": digest(result) if result.is_file() else None,
        "result_status": result_status, "result_parse_error": result_parse_error,
        "post_integrity": str(post_path),
        "post_integrity_sha256": digest(post_path), "post_unchanged": post["unchanged"],
        "credited_pass": credited, "new_preflight_subprocess_invocations": 1 if error is None else 0,
        "mathematical_execution": False, "protected_files_written": 0,
        "old_preflights_executed": 0, "Lean_executions": 0, "victory": False,
    }
    exclusive_json(receipt, final)
    print(json.dumps({"receipt": str(receipt), "receipt_sha256": digest(receipt),
                      "actual_exit_code": exit_code, "credited_pass": credited,
                      "result_sha256": final["result_sha256"],
                      "post_integrity_sha256": final["post_integrity_sha256"],
                      "changed_post_inputs": len(post["changed"]),
                      "mathematical_execution": False, "victory": False},
                     indent=2, sort_keys=True))
    if error is not None:
        return 2
    return 0 if credited else (int(exit_code) if exit_code else 1)


if __name__ == "__main__":
    raise SystemExit(main())
