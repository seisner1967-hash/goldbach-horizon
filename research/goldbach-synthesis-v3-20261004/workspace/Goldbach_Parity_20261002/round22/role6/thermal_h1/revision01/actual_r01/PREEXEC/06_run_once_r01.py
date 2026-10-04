"""Metadata gate/capture launcher for a distinct new component attempt.

Never imports an analytic module. Only the recorded child is the math actor.
The unique actual directory consumes the attempt, including an early failure.
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
BASE = HERE.parent.parent.parent.parent
EXPECTED_GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_thermal_component_r01_authorization.json"
PREPARATION = HERE / "preparation_r01.json"
ACTUAL = HERE / "actual_r01"
SCOPE = "THERMAL_COMPONENT_R01_AUX_ONLY"
BANK = "THERMAL_COMPONENT_R01_AUX22"


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


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
    if gate_path != EXPECTED_GATE.resolve() or sha(gate_path) != args.root_authorization_sha256:
        raise RuntimeError("exact distinct component root gate and byte hash required")
    prep_sha = sha(PREPARATION)
    prep = json.loads(PREPARATION.read_text(encoding="utf-8"))
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    if (gate.get("status") != "AUTHORIZED" or gate.get("actor") != "ROLE6"
            or gate.get("bank_id") != BANK or gate.get("scope") != SCOPE):
        raise RuntimeError("root component authorization scope missing")
    if gate.get("preparation_sha256") != prep_sha or gate.get("bindings") != prep["bindings"]:
        raise RuntimeError("exact frozen preparation/bindings not authorized")
    for binding in prep["bindings"]:
        path = Path(binding["path"]).resolve()
        if sha(path) != binding["sha256"] or path.stat().st_size != binding["bytes"]:
            raise RuntimeError("pre-execution binding changed:" + str(path))
    runtime = Path(prep["runtime_path"]).resolve()
    if (Path(sys.executable).resolve() != runtime or sys.flags.utf8_mode != 1
            or sys.dont_write_bytecode is not True):
        raise RuntimeError("frozen Python -B -X utf8 required")
    ACTUAL.mkdir(exist_ok=False)
    token = uuid.uuid4().hex
    create_json(ACTUAL / "attempt_reservation.json", {
        "time_utc": utc(), "attempt_token": token, "scope": SCOPE,
        "gate_sha256": sha(gate_path), "no_math_started_yet": True})
    capture_dir = ACTUAL / "PREEXEC"
    capture_dir.mkdir()
    captures = []
    for index, binding in enumerate(prep["bindings"]):
        path = Path(binding["path"]).resolve()
        destination = capture_dir / (str(index).zfill(2) + "_" + path.name)
        shutil.copyfile(path, destination)
        if sha(destination) != binding["sha256"]:
            raise RuntimeError("PREEXEC byte copy mismatch")
        captures.append({"source": str(path), "copy": str(destination),
                         "sha256": sha(destination), "phase": "PREEXEC"})
    for name, path in (("preparation", PREPARATION), ("root_gate", gate_path)):
        destination = capture_dir / (name + ".json")
        shutil.copyfile(path, destination)
        if sha(destination) != sha(path):
            raise RuntimeError("PREEXEC preparation/gate copy mismatch")
        captures.append({"source": str(path), "copy": str(destination),
                         "sha256": sha(destination), "phase": "PREEXEC"})
    create_json(ACTUAL / "PREEXEC_captures.json", {"captures": captures,
                "attempt_token": token, "math_started": False})
    output = ACTUAL / "result_r01.json"
    start_path = ACTUAL / "actual_START.json"
    command = [str(runtime), "-B", "-X", "utf8", str(HERE / "producer_r01.py"),
               "--contract", str(HERE / "contract_r01.json"),
               "--output", str(output), "--actual-start", str(start_path)]
    start = utc()
    create_json(start_path, {"time_utc": start, "attempt_token": token, "command": command,
                "gate_path": str(gate_path), "gate_sha256": sha(gate_path), "scope": SCOPE,
                "preparation_sha256": prep_sha, "captures_complete": True})
    print(json.dumps({"actual_START": start, "attempt_token": token, "command": command},
                     sort_keys=True), flush=True)
    log = ACTUAL / "actual.log"
    launch_error = None
    exit_code = None
    try:
        with log.open("xb") as stream:
            process = subprocess.Popen(command, cwd=str(HERE), stdout=stream, stderr=subprocess.STDOUT)
            exit_code = process.wait()
    except BaseException as error:
        launch_error = type(error).__name__ + ": " + str(error)
    finish = utc()
    post, intact = [], True
    for binding in prep["bindings"]:
        path = Path(binding["path"]).resolve()
        actual_sha = sha(path)
        equal = actual_sha == binding["sha256"] and path.stat().st_size == binding["bytes"]
        intact = intact and equal
        post.append({"path": str(path), "expected_sha256": binding["sha256"],
                     "actual_sha256": actual_sha, "unchanged": equal, "phase": "POSTEXEC"})
    prep_intact = sha(PREPARATION) == prep_sha
    gate_intact = sha(gate_path) == args.root_authorization_sha256
    intact = intact and prep_intact and gate_intact
    create_json(ACTUAL / "POSTEXEC_integrity.json", {
        "bindings": post, "all_unchanged": intact,
        "preparation_unchanged": prep_intact, "gate_unchanged": gate_intact,
        "no_old_producer_or_preflight_reexecuted": True})
    certificates = ACTUAL / "sqrt_certificates_r01.jsonl"
    receipt = {"schema": "round22.thermal_component.actual_receipt.r01", "scope": SCOPE,
               "attempt_token": token, "actual_START": start, "actual_FINISH": finish,
               "command": command, "exit_code": exit_code, "launch_error": launch_error,
               "post_integrity": intact, "log_sha256": sha(log) if log.exists() else None,
               "result_sha256": sha(output) if output.exists() else None,
               "sqrt_certificate_sha256": sha(certificates) if certificates.exists() else None,
               "preparation_sha256": prep_sha, "root_gate_sha256": args.root_authorization_sha256,
               "Lean_invocations": 0, "global_H1_invocations": 0, "old_bank_replays": 0,
               "coefficient_N_invocations": 0, "D_N_claim": False, "WIN": False,
               "no_credit_if_bound_source_mutated": True}
    create_json(ACTUAL / "actual_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True), flush=True)
    return 3 if launch_error is not None or not intact else exit_code


if __name__ == "__main__":
    raise SystemExit(main())
