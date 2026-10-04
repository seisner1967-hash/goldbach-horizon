"""One-attempt launcher.  It is source-only until a distinct root gate exists.

Hashing/captures are metadata; only the recorded subprocess is the math actor.
No original source, frozen prior artifact, or root coordinator file is written.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import uuid

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent
EXPECTED_GATE = BASE / ".arbor" / "sessions" / "parity" / ".coordinator" / "messages" / "round22_epstein_authorization.json"
PREPARATION = HERE / "epstein_preparation22.json"
ACTUAL = HERE / "actual_epstein22"


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            h.update(block)
    return h.hexdigest()


def create_json(path, data):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(data, stream, indent=2, sort_keys=True)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-authorization", required=True)
    parser.add_argument("--root-authorization-sha256", required=True)
    args = parser.parse_args()
    gate_path = Path(args.root_authorization).resolve()
    if gate_path != EXPECTED_GATE.resolve():
        raise RuntimeError("distinct exact root gate path required")
    if sha(gate_path) != args.root_authorization_sha256:
        raise RuntimeError("root gate byte hash mismatch")
    prep_sha = sha(PREPARATION)
    prep = json.loads(PREPARATION.read_text(encoding="utf-8"))
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    if gate.get("status") != "AUTHORIZED" or gate.get("actor") != "ROLE6":
        raise RuntimeError("root has not authorized this actor")
    if gate.get("bank_id") != "EPSTEIN_UNFOLDING_AUX22":
        raise RuntimeError("different bank gate")
    if gate.get("scope") != "EPSTEIN_UNFOLDING_AUX_ONLY":
        raise RuntimeError("scope mismatch")
    if gate.get("preparation_sha256") != prep_sha:
        raise RuntimeError("preparation gate mismatch")
    if gate.get("bindings") != prep["bindings"]:
        raise RuntimeError("source/input/runtime bindings not reviewed exactly")
    for binding in prep["bindings"]:
        path = Path(binding["path"]).resolve()
        if sha(path) != binding["sha256"]:
            raise RuntimeError("pre-execution source/input/runtime mutation: " + str(path))
    runtime = Path(prep["runtime_path"]).resolve()
    if Path(sys.executable).resolve() != runtime:
        raise RuntimeError("prepared Python runtime is required")
    # The reserved directory is intentionally never created by preparation.
    # Its atomic creation consumes the sole authorized attempt even if launch fails.
    ACTUAL.mkdir(exist_ok=False)
    token = uuid.uuid4().hex
    create_json(ACTUAL / "attempt_reservation.json", {
        "time_utc": utc(), "attempt_token": token,
        "scope": "EPSTEIN_UNFOLDING_AUX_ONLY", "gate_sha256": sha(gate_path),
        "no_math_started_yet": True})
    capture_dir = ACTUAL / "PREEXEC"
    capture_dir.mkdir()
    captures = []
    for i, binding in enumerate(prep["bindings"]):
        path = Path(binding["path"]).resolve()
        dest = capture_dir / (str(i).zfill(2) + "_" + path.name)
        shutil.copyfile(path, dest)
        if sha(dest) != binding["sha256"]:
            raise RuntimeError("PREEXEC copy mismatch")
        captures.append({"source": str(path), "copy": str(dest),
                         "sha256": sha(dest), "phase": "PREEXEC"})
    for name, path in (("preparation", PREPARATION), ("root_gate", gate_path)):
        dest = capture_dir / (name + ".json")
        shutil.copyfile(path, dest)
        captures.append({"source": str(path), "copy": str(dest),
                         "sha256": sha(dest), "phase": "PREEXEC"})
    create_json(ACTUAL / "PREEXEC_captures.json", {"captures": captures,
                "attempt_token": token, "math_started": False})
    output = ACTUAL / "epstein_result22.json"
    command = [str(runtime), "-B", "-X", "utf8", str(HERE / "epstein_bank22.py"),
               "--contract", str(HERE / "epstein_contract22.json"),
               "--output", str(output)]
    start = utc()
    create_json(ACTUAL / "actual_START.json", {"time_utc": start,
                "attempt_token": token, "command": command,
                "gate_path": str(gate_path), "gate_sha256": sha(gate_path),
                "scope": "EPSTEIN_UNFOLDING_AUX_ONLY",
                "preparation_sha256": prep_sha, "captures_complete": True})
    print(json.dumps({"actual_START": start, "attempt_token": token,
                      "command": command}, sort_keys=True), flush=True)
    log = ACTUAL / "actual.log"
    launch_error = None
    exit_code = None
    try:
        with log.open("xb") as stream:
            process = subprocess.Popen(command, cwd=str(HERE), stdout=stream,
                                       stderr=subprocess.STDOUT)
            exit_code = process.wait()
    except BaseException as exc:
        launch_error = type(exc).__name__ + ": " + str(exc)
    finish = utc()
    post = []
    intact = True
    for binding in prep["bindings"]:
        path = Path(binding["path"]).resolve()
        actual_sha = sha(path)
        equal = actual_sha == binding["sha256"]
        intact = intact and equal
        post.append({"path": str(path), "expected_sha256": binding["sha256"],
                     "actual_sha256": actual_sha, "unchanged": equal,
                     "phase": "POSTEXEC"})
    prep_intact = sha(PREPARATION) == prep_sha
    gate_intact = sha(gate_path) == args.root_authorization_sha256
    intact = intact and prep_intact and gate_intact
    create_json(ACTUAL / "POSTEXEC_integrity.json", {
        "bindings": post, "all_unchanged": intact,
        "preparation_unchanged": prep_intact, "gate_unchanged": gate_intact,
        "this_is_not_a_second_conservation_preflight": True})
    receipt = {"schema": "round22.epstein_unfolding_aux.actual_receipt.v1",
               "scope": "EPSTEIN_UNFOLDING_AUX_ONLY", "attempt_token": token,
               "actual_START": start, "actual_FINISH": finish,
               "command": command, "exit_code": exit_code,
               "launch_error": launch_error, "post_integrity": intact,
               "log_sha256": sha(log) if log.exists() else None,
               "result_sha256": sha(output) if output.exists() else None,
               "sqrt_certificate_sha256": sha(ACTUAL / "epstein_sqrt_certificates22.jsonl") if (ACTUAL / "epstein_sqrt_certificates22.jsonl").exists() else None,
               "preparation_sha256": prep_sha,
               "root_gate_sha256": args.root_authorization_sha256,
               "Lean_invocations": 0, "coefficient_N_invocations": 0,
               "heat_invocations": 0, "Weil_invocations": 0,
               "no_credit_if_bound_source_mutated": True}
    create_json(ACTUAL / "actual_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True), flush=True)
    if launch_error is not None or not intact:
        return 3
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
