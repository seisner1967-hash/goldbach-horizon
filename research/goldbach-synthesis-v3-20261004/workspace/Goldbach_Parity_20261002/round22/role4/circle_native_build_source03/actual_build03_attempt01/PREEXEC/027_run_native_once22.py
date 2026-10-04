"""SOURCE ONLY parent for a future ROOT-authorized fixed native coefficient run.

No preparation, gate, binaries or attempt exists in this packet. Never imported.
Compile/build and numeric authorities are distinct; this launcher never compiles.
"""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[2]
PREP = HERE / "runtime_preparation22.json"
GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_native_full02_authorization.json"
ACTUAL = HERE / "actual_native02_attempt01"
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PY_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
REGISTRY = BASE / "round22/previous_artifacts_sha256.json"
REG_SHA = "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99"
FIXED = {"scope": "NATIVE_FULL_N1E8_ONLY", "fixed_N": 100000000,
    "fixed_K": 134217728, "fixed_S": "288230376151711744", "max_children": 2,
    "max_retries": 0, "wall_seconds": 3600, "output_bytes": 2147483648,
    "commit_bytes": 2147483648, "rss_bytes": 2147483648,
    "log_bytes": 1048576, "metadata_bytes": 16777216, "capture_bytes": 33554432}
ENTERED = time.monotonic()
OWNED_ATTEMPT = False


def utc():
    return datetime.now(timezone.utc).isoformat()


def need(ok, text):
    if not ok:
        raise RuntimeError(text)


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for data in iter(lambda: f.read(1 << 20), b""):
            need(time.monotonic() < ENTERED + FIXED["wall_seconds"], "PARENT_WALL_BUDGET_EXHAUSTED")
            h.update(data)
    return h.hexdigest()


def read(path, limit=16777216):
    need(path.stat().st_size <= limit, "CONTROL_SIZE_LIMIT")
    return json.loads(path.read_text(encoding="utf-8-sig"))


def key(path):
    return str(path.resolve()).casefold()


def binding(row):
    p = Path(row["path"])
    need(p.is_absolute() and p.is_file(), "BINDING_FILE_MISSING")
    need(not (getattr(p.lstat(), "st_file_attributes", 0) & 0x400), "REPARSE_BINDING")
    need(p.stat().st_size == row["bytes"] and sha(p) == row["sha256"], "BINDING_CHANGED:" + str(p))


def archives():
    need(sha(REGISTRY) == REG_SHA, "PROTECTED_REGISTRY_CHANGED")
    registry = read(REGISTRY)
    need(len(registry["sha256"]) == 3089, "ARCHIVE_COUNT_CHANGED")
    for name, expected in registry["sha256"].items():
        p = (BASE / name).resolve()
        need(p.is_relative_to(BASE.resolve()) and sha(p) == expected, "ARCHIVE_CHANGED:" + name)
    return {"registry_sha256": REG_SHA, "count": 3089, "all_intact": True}


class Budget:
    def __init__(self):
        self.metadata = self.logs = 0
        self.lock = threading.Lock()
        self.log_files = {}

    def record(self, name, data):
        encoded = (json.dumps(data, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
        need(len(encoded) <= 1048576, "SINGLE_METADATA_FILE_TOO_LARGE")
        with self.lock:
            need(self.metadata + len(encoded) <= FIXED["metadata_bytes"] - 65536,
                 "METADATA_RESERVE_EXHAUSTED")
            with (ACTUAL / name).open("xb") as f:
                f.write(encoded)
            self.metadata += len(encoded)

    def write_log(self, label, channel, data):
        with self.lock:
            room = FIXED["log_bytes"] - self.logs
            part = data[:room]
            if part:
                self.log_files[label, channel].write(part)
                self.log_files[label, channel].flush()
                self.logs += len(part)
            need(len(data) <= room, "PIPE_BYTE_CAP_EXHAUSTED")

    def open_logs(self, label):
        for channel in ("stdout", "stderr"):
            self.log_files[label, channel] = (ACTUAL / (label + "." + channel + ".log")).open("xb")

    def close_logs(self):
        for f in self.log_files.values():
            f.close()


def output_guard():
    total = 0
    for p in ACTUAL.rglob("*"):
        need(not (getattr(p.lstat(), "st_file_attributes", 0) & 0x400), "REPARSE_OUTPUT")
        if p.is_file():
            total += p.stat().st_size
    need(total <= FIXED["output_bytes"], "ATTEMPT_OUTPUT_CAP_EXHAUSTED")
    payload = ACTUAL / "payload"
    if payload.exists():
        allowed = {"factors.bin": 400000020, "records.bin": 800000040, "producer.txt": 4096}
        for p in payload.iterdir():
            need(p.is_file() and p.name in allowed and p.stat().st_size <= allowed[p.name],
                 "PAYLOAD_FORMAT_SIZE_LIMIT")
    # Source programs write only these fixed format files, not arbitrary paths.
    # The check is a monitor, not a filesystem quota against an untrusted binary.


def load_backend():
    spec = importlib.util.spec_from_file_location("fixed_windows_job22", HERE / "windows_job22.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def preflight():
    global OWNED_ATTEMPT
    need(key(Path(sys.executable)) == key(PYTHON) and sha(PYTHON) == PY_SHA, "CANONICAL_PYTHON_REQUIRED")
    prep_sha, gate_sha = sha(PREP), sha(GATE)
    prep, gate = read(PREP), read(GATE)
    need(prep.get("status") == "NATIVE_RUNTIME_METADATA_PREPARED", "NO_NATIVE_RUNTIME_PREPARATION")
    need(gate.get("status") == "AUTHORIZED" and gate.get("preparation_sha256") == prep_sha,
         "NO_EXACT_ROOT_GATE")
    for name, value in FIXED.items():
        need(prep.get(name) == value and gate.get(name) == value, "FIXED_GATE_OR_RESOURCE_MISMATCH:" + name)
    manifest = Path(prep["manifest_path"])
    need(sha(manifest) == prep["manifest_sha256"], "MANIFEST_CHANGED")
    rows = read(manifest)["bindings"]
    by_path = {key(Path(b["path"])): b for b in rows}
    need(len(rows) == len(by_path) == prep["binding_count"], "BINDING_DUPLICATE_OR_COUNT")
    snapshot, handoff = HERE / "closure_snapshot22.json", HERE / "source_handoff22.json"
    need(sha(snapshot) == prep["closure_snapshot_sha256"] and
         sha(handoff) == prep["source_handoff_sha256"], "SOURCE_CLOSURE_CHANGED")
    expected_rows = {}
    for row in read(snapshot)["bindings"] + read(handoff)["bindings"]:
        row_key = key(Path(row["path"]))
        if row_key in expected_rows:
            need((expected_rows[row_key]["sha256"], expected_rows[row_key]["bytes"]) ==
                 (row["sha256"], row["bytes"]), "SOURCE_SNAPSHOT_BINDING_CONFLICT")
        expected_rows[row_key] = row
    expected = set(expected_rows)
    build = Path(prep["build_receipt_path"])
    review = Path(gate["independent_native_source_review_path"])
    loader_review = Path(gate["native_loader_closure_review_path"])
    bins = [HERE / "build-final/producer_dit22.exe", HERE / "build-final/checker_dif22.exe"]
    expected.update(map(key, bins + [build, review, loader_review, snapshot, handoff]))
    need(set(by_path) == expected, "EXACT_RUNTIME_BINDING_PATH_SET_MISMATCH")
    for row_key, expected_row in expected_rows.items():
        actual_row = by_path[row_key]
        need((actual_row["sha256"], actual_row["bytes"]) ==
             (expected_row["sha256"], expected_row["bytes"]), "FROZEN_SOURCE_BINDING_BYTES_MISMATCH")
        if expected_row.get("capture", False):
            need(actual_row.get("capture", False), "REQUIRED_SOURCE_CAPTURE_OMITTED")
    for row in rows:
        binding(row)
    need(sha(build) == prep["build_receipt_sha256"] and
         sha(review) == gate["independent_native_source_review_sha256"] and
         sha(loader_review) == gate["native_loader_closure_review_sha256"], "REVIEW_OR_BUILD_CHANGED")
    build_data = read(build)
    need(build_data.get("status") == "NATIVE_BUILD_EXIT0" and
         build_data.get("child_exit_codes") == [0, 0], "NO_REAL_TWO_BINARY_BUILD")
    need(build_data.get("build_plan_sha256") == sha(HERE / "build_plan22.json"),
         "BUILD_PLAN_LINK_MISMATCH")
    need(build_data.get("source_sha256") == [sha(HERE / "producer_dit22.cpp"), sha(HERE / "checker_dif22.cpp")],
         "BUILD_SOURCE_LINK_MISMATCH")
    need(build_data.get("binary_sha256") == [sha(p) for p in bins], "BUILD_BINARY_LINK_MISMATCH")
    loader_data = read(loader_review)
    need(loader_data.get("status") == "NATIVE_LOADER_CLOSURE_REVIEWED_WITH_WINDOWS_TRUST_BASE" and
         loader_data.get("binary_sha256") == [sha(p) for p in bins] and
         loader_data.get("all_non_OS_imports_bound") is True,
         "LOADER_CLOSURE_STILL_OPEN")
    need(set(p.name for p in bins[0].parent.iterdir()) == {p.name for p in bins},
         "BUILD_FINAL_DIRECTORY_NOT_TWO_EXES_ONLY")
    controls = {key(PREP): (PREP, prep_sha), key(GATE): (GATE, gate_sha),
        key(manifest): (manifest, prep["manifest_sha256"]),
        key(review): (review, gate["independent_native_source_review_sha256"]),
        key(loader_review): (loader_review, gate["native_loader_closure_review_sha256"])}
    for row in rows:
        if row.get("capture", False):
            p = Path(row["path"])
            if key(p) in controls:
                need(controls[key(p)][1] == row["sha256"], "CONFLICTING_CAPTURE_EXPECTATION")
            controls[key(p)] = (p, row["sha256"])
    archive_state = archives()
    need(not ACTUAL.exists(), "ONE_ATTEMPT_ALREADY_EXISTS")
    ACTUAL.mkdir()
    OWNED_ATTEMPT = True
    (ACTUAL / "tmp").mkdir()
    (ACTUAL / "PREEXEC").mkdir()
    captures, copied = [], 0
    try:
        for index, (p, expected_sha) in enumerate(controls.values()):
            need(sha(p) == expected_sha, "PRE_CAPTURE_ORIGINAL_CHANGED")
            copied += p.stat().st_size
            need(copied <= FIXED["capture_bytes"], "PRE_CAPTURE_BYTES_LIMIT")
            dst = ACTUAL / "PREEXEC" / (str(index).zfill(3) + "_" + p.name)
            shutil.copyfile(p, dst)
            need(sha(dst) == expected_sha, "PRE_CAPTURE_COPY_CHANGED")
            captures.append({"original": str(p), "copy": str(dst), "sha256": expected_sha})
    except BaseException as error:
        # No native child exists; the attempt is consumed and remains preserved.
        with (ACTUAL / "PRE_CONTROL_FAILURE.json").open("x", encoding="utf-8") as f:
            json.dump({"utc": utc(), "status": "METADATA_FAILURE_NO_NATIVE_CHILD",
                "failure": type(error).__name__ + ":" + str(error), "retry_count": 0,
                "formal_primitives": False, "D_N": False, "WIN": False}, f)
        raise
    return prep_sha, rows, controls, captures, archive_state, bins


def main():
    # Absence of either future file aborts before creating an attempt or child.
    prep_sha, rows, controls, captures, archived, bins = preflight()
    budget, results, failure = Budget(), [], None
    started, deadline = ENTERED, None
    budget.record("PRE.json", {"utc": utc(), "preparation_sha256": prep_sha,
        "binding_count": len(rows), "captures": captures, "archives": archived,
        "runtime_copied": False, "formal_primitives": False, "D_N": False, "WIN": False})
    try:
        backend = load_backend()
        deadline = ENTERED + FIXED["wall_seconds"]
        for label, exe in zip(("producer", "checker"), bins):
            need(time.monotonic() < deadline, "SHARED_WALL_BUDGET_EXHAUSTED")
            budget.open_logs(label)
            budget.record(label + "_START_REQUEST.json", {"utc": utc(), "executable": str(exe),
                "sha256": sha(exe), "ordinal": len(results) + 1, "max_children": 2,
                "max_retries": 0, "created": False, "resumed": False})

            def created(pid, tag=label):
                budget.record(tag + "_CREATED_SUSPENDED.json", {"utc": utc(), "pid": pid,
                    "resumed": False, "before_job_assignment": True})

            def resumed(pid, tag=label):
                budget.record(tag + "_START.json", {"utc": utc(), "pid": pid,
                    "job_assigned": True, "commit_and_working_set_quotas_read_back": True})

            result = backend.run_child(exe, ACTUAL / "payload", ACTUAL, deadline,
                FIXED["commit_bytes"], FIXED["rss_bytes"],
                lambda channel, data, tag=label: budget.write_log(tag, channel, data),
                output_guard, created, resumed)
            result["utc_FIN"] = utc()
            result["label"] = label
            budget.record(label + "_FIN.json", result)
            results.append(result)
            output_guard()
            need(result["exit_code"] == 0 and result["termination_reason"] is None and
                 result["wait_signalled"] and result["api_or_control_error"] is None and
                 not result["pipe_faults"], "STOP_FIRST_FAIL:" + label)
            # The checker may only inspect the original producer bytes.
            payload = ACTUAL / "payload"
            if label == "producer":
                payload_before = {p.name: sha(p) for p in payload.iterdir()}
                budget.record("producer_payload_hashes.json", payload_before)
        need({p.name: sha(p) for p in (ACTUAL / "payload").iterdir()} == payload_before,
             "CHECKER_CHANGED_PRODUCER_PAYLOAD")
    except BaseException as e:
        failure = type(e).__name__ + ":" + str(e)
    finally:
        budget.close_logs()
    if failure is None:
        try:
            checker_text = (ACTUAL / "checker.stdout.log").read_text(encoding="ascii")
            need(checker_text.startswith("EXACT_INTEGER_PROJECTION_CHECKED_PENDING_PRIMITIVE_PROOF\n") and
                checker_text.endswith("FORMAL_PRIMITIVES false\nSPECTRAL_H1 false\nD_N false\nWIN false\n"),
                "CHECKER_SUCCESS_RECORD_MISSING")
        except BaseException as e:
            failure = type(e).__name__ + ":" + str(e)
    conservation_error = None
    try:
        for row in rows:
            binding(row)
        for p, expected_sha in controls.values():
            need(sha(p) == expected_sha, "POST_CONTROL_ORIGINAL_CHANGED")
        for captured in captures:
            need(sha(Path(captured["original"])) == captured["sha256"] and
                 sha(Path(captured["copy"])) == captured["sha256"], "POST_CAPTURE_ORIGINAL_OR_COPY_CHANGED")
        need(archives() == archived, "POST_ARCHIVE_CHANGED")
        output_guard()
    except BaseException as e:
        conservation_error = type(e).__name__ + ":" + str(e)
    success = failure is None and conservation_error is None and len(results) == 2
    status = ("NATIVE_NUMERICAL_COEFFICIENT_AUX_CHECKED_PENDING_FORMAL_PRIMITIVES"
              if success else "NATIVE_STOP_NO_MATHEMATICAL_VERDICT")
    budget.record("POST.json", {"utc": utc(), "conservation_error": conservation_error,
        "all_bindings_controls_captures_archives_intact": conservation_error is None})
    budget.record("receipt.json", {"status": status, "utc_FIN": utc(),
        "preparation_sha256": prep_sha, "attempt_count": 1, "retry_count": 0,
        "children_returned": len(results), "results": results, "failure": failure,
        "conservation_error": conservation_error, "elapsed_parent_seconds": time.monotonic() - started,
        "limits": FIXED, "formal_primitives": False, "spectral_H1": False, "D_N": False, "WIN": False})
    print(status)
    return 0 if success else 1


if __name__ == "__main__":
    def emergency_stop():
        # This watchdog also covers metadata/hash housekeeping. OS scheduling
        # latency is not a measured strict millisecond deadline. Abrupt exit
        # closes Job handles, hence KILL_ON_JOB_CLOSE. No success is possible.
        if OWNED_ATTEMPT:
            try:
                with (ACTUAL / "WATCHDOG_TERMINATION_REQUEST.json").open("x", encoding="utf-8") as f:
                    json.dump({"utc": utc(), "status": "HARD_WALL_NO_VERDICT_POST_UNVERIFIED",
                        "wall_seconds": 3600, "conservation_verified": False,
                        "formal_primitives": False, "D_N": False, "WIN": False}, f)
            except BaseException:
                pass
        os._exit(124)

    watchdog = threading.Timer(max(0, ENTERED + FIXED["wall_seconds"] - time.monotonic()), emergency_stop)
    watchdog.daemon = True
    watchdog.start()
    try:
        raise SystemExit(main())
    except Exception as error:
        print("NATIVE_PARENT_CONTROL_ERROR_NO_VERDICT", type(error).__name__, str(error), file=sys.stderr)
        raise SystemExit(2)
    finally:
        watchdog.cancel()
