"""SOURCE ONLY. No child or parsing invocation during packet construction.

Future ROOT-specific gate, one child, 60 seconds, 1 MiB total attempt outputs.
Copies only small source/control files; runtime/archive objects are hash-bound.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
import uuid

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[2]
PREPARATION = HERE / "preparation22.json"
ACTUAL = HERE / "actual_attempt01"
GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_parameter_guard01_authorization.json"
REGISTRY = BASE / "round22/previous_artifacts_sha256.json"
REGISTRY_SHA = "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99"
SCOPE = "PARAMETER_GUARD01_ONLY"
CAP = 1048576


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for data in iter(lambda: f.read(1048576), b""):
            h.update(data)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write(path, data):
    with path.open("x", encoding="utf-8", newline="\n") as f:
        json.dump(data, f, sort_keys=True, indent=2)
        f.write("\n")


def check_binding(binding):
    p = Path(binding["path"])
    if p.stat().st_size != binding["bytes"] or sha(p) != binding["sha256"]:
        raise RuntimeError("INPUT_BYTES_CHANGED:" + str(p))


def archives():
    if sha(REGISTRY) != REGISTRY_SHA:
        raise RuntimeError("ARCHIVE_REGISTRY_CHANGED")
    r = read(REGISTRY)
    if r["file_count"] != 3089 or len(r["sha256"]) != 3089:
        raise RuntimeError("ARCHIVE_COUNT_CHANGED")
    for name, expected in r["sha256"].items():
        path = (BASE / name).resolve()
        if not path.is_relative_to(BASE.resolve()) or sha(path) != expected:
            raise RuntimeError("PROTECTED_ARCHIVE_CHANGED:" + name)
    return {"count": 3089, "unchanged": True, "registry_sha256": REGISTRY_SHA}


def output_size():
    return sum(p.stat().st_size for p in ACTUAL.rglob("*") if p.is_file())


def main():
    if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
            and sys.flags.utf8_mode == 1):
        raise RuntimeError("CANONICAL_PYTHON_-I_-S_-B_-X_UTF8_REQUIRED")
    prep_sha = sha(PREPARATION)
    prep = read(PREPARATION)
    manifest = Path(prep["manifest_path"])
    if sha(manifest) != prep["manifest_sha256"]:
        raise RuntimeError("MANIFEST_CHANGED")
    inputs = read(manifest)["bindings"]
    paths = [str(Path(b["path"]).resolve()).casefold() for b in inputs]
    if len(paths) != len(set(paths)) or len(inputs) != prep["binding_count"]:
        raise RuntimeError("INPUT_SET_NOT_EXACT")
    for item in inputs:
        check_binding(item)
    gate_sha = sha(GATE)
    gate = read(GATE)
    required = {"status": "AUTHORIZED", "scope": SCOPE, "preparation_sha256": prep_sha,
                "max_children": 1, "max_retries": 0, "wall_seconds": 60,
                "output_bytes": CAP}
    for key, expected in required.items():
        if gate.get(key) != expected:
            raise RuntimeError("ROOT_GATE_FIELD_MISMATCH:" + key)
    review = Path(gate["independent_source_review_path"])
    if sha(review) != gate["independent_source_review_sha256"]:
        raise RuntimeError("INDEPENDENT_SOURCE_REVIEW_BYTES_CHANGED")
    # ROOT authorizes this exact review, not a numerical PASS premise.
    previous = archives()
    ACTUAL.mkdir(exist_ok=False)
    copies = ACTUAL / "PREEXEC_FILES"
    copies.mkdir()
    token = str(uuid.uuid4())
    captured = []
    controls = [PREPARATION, manifest, GATE, review]
    controls += [Path(b["path"]) for b in inputs if b.get("capture", False)]
    seen = set()
    for path in controls:
        p = path.resolve()
        if str(p).casefold() in seen:
            continue
        seen.add(str(p).casefold())
        destination = copies / (str(len(captured)).zfill(3) + "_" + p.name)
        shutil.copyfile(p, destination)
        expected = sha(p)
        if sha(destination) != expected:
            raise RuntimeError("PREEXEC_COPY_CHANGED")
        captured.append({"original": str(p), "copy": str(destination),
                         "sha256": expected, "bytes": destination.stat().st_size})
    controller = next(Path(x["copy"]) for x in captured if Path(x["original"]).name == "parameter_guard22.py")
    model = next(Path(x["copy"]) for x in captured if Path(x["original"]).name == "fixed_parameter_log_model22.py")
    python = Path(prep["canonical_python"])
    if Path(sys.executable).resolve() != python.resolve():
        raise RuntimeError("CANONICAL_PYTHON_PATH_MISMATCH")
    command = [str(python), "-I", "-S", "-B", "-X", "utf8", str(controller), str(model)]
    write(ACTUAL / "PREEXEC.json", {"time_utc": utc(), "token": token,
          "input_count": len(inputs), "all_inputs_intact": True, "archives": previous,
          "gate_sha256": gate_sha, "captured": captured, "children_started": 0})
    if output_size() > CAP // 2:
        raise RuntimeError("CONTROL_CAPTURE_PAYLOAD_TOO_LARGE")
    child_start = utc()
    write(ACTUAL / "START.json", {"time_utc": child_start, "token": token,
          "command": command, "max_children": 1, "max_retries": 0,
          "start_transition_requested": True, "actual_pid": None})
    exit_code, stop, spawn_error, pid = None, None, None, None
    started_monotonic = time.monotonic()
    with (ACTUAL / "stdout.log").open("xb") as out, (ACTUAL / "stderr.log").open("xb") as err:
        child = None
        try:
            child = subprocess.Popen(command, stdout=out, stderr=err, cwd=str(ACTUAL))
            pid = child.pid
            write(ACTUAL / "SPAWN.json", {"time_utc": utc(), "token": token, "actual_pid": pid})
            while child.poll() is None:
                if time.monotonic() - started_monotonic >= 60:
                    stop = "RESOURCE_LIMIT_NO_VERDICT_WALL"
                    child.kill()
                    break
                if output_size() > CAP - 65536:
                    stop = "RESOURCE_LIMIT_NO_VERDICT_OUTPUT"
                    child.kill()
                    break
                time.sleep(0.05)
            exit_code = child.wait()
        except BaseException as error:
            spawn_error = type(error).__name__ + ":" + str(error)
            if child is not None:
                if child.poll() is None:
                    child.kill()
                exit_code = child.wait()
    finish = utc()
    conservation_error = None
    try:
        for item in inputs:
            check_binding(item)
        after = archives()
        if sha(PREPARATION) != prep_sha or sha(GATE) != gate_sha:
            raise RuntimeError("CONTROL_OR_GATE_CHANGED")
        for item in captured:
            if sha(Path(item["copy"])) != item["sha256"]:
                raise RuntimeError("CAPTURE_CHANGED")
    except BaseException as error:
        conservation_error = type(error).__name__ + ":" + str(error)
        after = {"unchanged": False, "count": 3089}
    result, parse_error = None, None
    if exit_code == 0 and stop is None and spawn_error is None:
        try:
            result = read(ACTUAL / "stdout.log")
            if (result["schema"] != "ROUND22_PARAMETER_GUARD01_RESULT"
                    or result["scope"] != SCOPE
                    or result["status"] != "PARAMETER_GUARDS_AND_FIVE_LOG_SAMPLES_AUX_PASS"
                    or len(result["samples"]) != 5 or len(result["mutations"]) != 4
                    or not all(x["rejected"] for x in result["mutations"])
                    or any(result[key] for key in ("global_NTT_computed", "complete_catalogue_checked",
                                                  "coefficient_N_computed", "D_N", "WIN"))):
                raise RuntimeError("AUX_RESULT_SCOPE_OR_GUARDS")
        except BaseException as error:
            parse_error = type(error).__name__ + ":" + str(error)
    verdict = (result["status"] if result is not None and parse_error is None and stop is None
               and spawn_error is None and conservation_error is None else "AUX_NO_VERDICT")
    write(ACTUAL / "FIN.json", {"time_utc": finish, "token": token, "actual_pid": pid,
          "children_started": int(pid is not None), "exit_code": exit_code, "stop": stop,
          "spawn_error": spawn_error, "status": verdict})
    write(ACTUAL / "POSTEXEC.json", {"time_utc": utc(), "input_count": len(inputs),
          "all_inputs_intact": conservation_error is None, "archives": after,
          "conservation_error": conservation_error, "parse_error": parse_error})
    write(ACTUAL / "receipt.json", {"schema": "ROUND22_PARAMETER_GUARD01_RECEIPT",
          "scope": SCOPE, "status": verdict, "START": child_start, "FIN": finish,
          "actual_pid": pid, "exit_code": exit_code, "children_started": int(pid is not None),
          "preparation_sha256": prep_sha, "gate_sha256": gate_sha,
          "stdout_sha256": sha(ACTUAL / "stdout.log"), "stderr_sha256": sha(ACTUAL / "stderr.log"),
          "conservation_error": conservation_error, "parse_error": parse_error,
          "global_projection": False, "formal_primitives": False, "D_N": False, "WIN": False})
    if output_size() > CAP:
        raise RuntimeError("FINAL_OUTPUT_LIMIT_NO_VERDICT")
    print(verdict)
    return 0 if verdict == "PARAMETER_GUARDS_AND_FIVE_LOG_SAMPLES_AUX_PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
