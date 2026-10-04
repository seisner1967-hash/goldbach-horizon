"""SOURCE ONLY: fixed two-target build, never imported/parsed/run.

No produced executable is run, probed, or given --version/help. A distinct
ROOT BUILD_ONLY gate, preparation and compiler-loader review are required.
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
NATIVE = HERE.with_name("circle_native_revision02")
PREP = HERE / "build_preparation22.json"
GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_native_build01_authorization.json"
ACTUAL = HERE / "actual_build01_attempt01"
OUT = NATIVE / "build-final"
BUILD_RECEIPT = NATIVE / "build_receipt22.json"
GXX = Path(r"C:\msys64\ucrt64\bin\g++.exe")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PY_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
REGISTRY = BASE / "round22/previous_artifacts_sha256.json"
REG_SHA = "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99"
FIXED = {"scope": "NATIVE_BUILD_ONLY_TWO_FIXED_TARGETS", "max_driver_invocations": 2,
    "max_retries": 0, "wall_seconds": 300, "max_active_job_processes": 16,
    "max_total_job_processes": 32, "commit_job_bytes": 2147483648,
    "rss_per_process_bytes": 2147483648, "sampled_job_rss_bytes": 4294967296,
    "log_bytes": 1048576, "capture_bytes": 33554432, "metadata_bytes": 16777216,
    "binary_bytes_each": 67108864, "temporary_bytes": 67108864,
    "output_bytes": 268435456, "produced_binary_invocations": 0}
ENTERED, OWNED = time.monotonic(), False


def utc():
    return datetime.now(timezone.utc).isoformat()


def need(ok, why):
    if not ok:
        raise RuntimeError(why)


def sha(p):
    h = hashlib.sha256()
    with p.open("rb") as f:
        for block in iter(lambda: f.read(1048576), b""):
            need(time.monotonic() < ENTERED + 300, "BUILD_PARENT_WALL_EXHAUSTED")
            h.update(block)
    return h.hexdigest()


def read(p):
    need(p.stat().st_size <= 16777216, "CONTROL_BYTES_LIMIT")
    return json.loads(p.read_text(encoding="utf-8-sig"))


def key(p):
    return str(p.resolve()).casefold()


def check_binding(row):
    p = Path(row["path"])
    need(not (getattr(p.lstat(), "st_file_attributes", 0) & 0x400), "REPARSE_INPUT")
    need(p.stat().st_size == row["bytes"] and sha(p) == row["sha256"], "INPUT_BYTES_CHANGED:" + str(p))


def archives():
    need(sha(REGISTRY) == REG_SHA, "REGISTRY_CHANGED")
    records = read(REGISTRY)["sha256"]
    need(len(records) == 3089, "ARCHIVE_COUNT")
    for name, expected in records.items():
        p = (BASE / name).resolve()
        need(p.is_relative_to(BASE.resolve()) and sha(p) == expected, "ARCHIVE_CHANGED:" + name)
    return {"count": 3089, "registry_sha256": REG_SHA, "all_intact": True}


class Writer:
    def __init__(self):
        self.log_bytes = self.meta_bytes = 0
        self.lock, self.logs = threading.Lock(), {}

    def record(self, name, value):
        data = (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
        need(len(data) <= 1048576 and self.meta_bytes + len(data) <= 16777216 - 65536, "META_BYTE_LIMIT")
        with (ACTUAL / name).open("xb") as f:
            f.write(data)
        self.meta_bytes += len(data)

    def open_logs(self, tag):
        for channel in ("stdout", "stderr"):
            self.logs[tag, channel] = (ACTUAL / (tag + "." + channel + ".log")).open("xb")

    def pipe(self, tag, channel, data):
        with self.lock:
            room = 1048576 - self.log_bytes
            part = data[:room]
            self.logs[tag, channel].write(part)
            self.logs[tag, channel].flush()
            self.log_bytes += len(part)
            need(len(data) <= room, "PIPE_BYTE_LIMIT")

    def close(self):
        for log in self.logs.values():
            log.close()


def dir_bytes(directory):
    count = 0
    if directory.exists():
        for p in directory.rglob("*"):
            need(not (getattr(p.lstat(), "st_file_attributes", 0) & 0x400), "REPARSE_OUTPUT")
            if p.is_file():
                count += p.stat().st_size
    return count


def output_guard():
    need(dir_bytes(ACTUAL) + dir_bytes(OUT) <= 268435456, "BUILD_OUTPUT_BYTE_LIMIT")
    need(dir_bytes(ACTUAL / "tmp") <= 67108864, "BUILD_TEMP_BYTE_LIMIT")
    allowed = {"producer_dit22.exe", "checker_dif22.exe"}
    for p in OUT.iterdir():
        need(p.is_file() and p.name in allowed and p.stat().st_size <= 67108864, "BUILD_BINARY_BYTE_LIMIT")


def preflight():
    need(key(Path(sys.executable)) == key(PYTHON) and sha(PYTHON) == PY_SHA, "CANONICAL_PYTHON_REQUIRED")
    prep_sha, gate_sha = sha(PREP), sha(GATE)
    prep, gate = read(PREP), read(GATE)
    need(prep.get("status") == "BUILD_ONLY_METADATA_PREPARED" and gate.get("status") == "AUTHORIZED" and
         gate.get("preparation_sha256") == prep_sha, "NO_EXACT_BUILD_ONLY_GATE")
    for field, fixed in FIXED.items():
        need(prep.get(field) == fixed and gate.get(field) == fixed, "BUILD_FIXED_GATE_MISMATCH:" + field)
    manifest = Path(prep["manifest_path"])
    need(sha(manifest) == prep["manifest_sha256"], "MANIFEST_CHANGED")
    rows = read(manifest)["bindings"]
    by_path = {key(Path(b["path"])): b for b in rows}
    need(len(rows) == len(by_path) == prep["binding_count"], "DUPLICATE_BINDING_OR_COUNT")
    fixed_controls = [(NATIVE / "closure_snapshot22.json", prep["closure_snapshot_sha256"]),
        (NATIVE / "source_handoff22.json", prep["native_source_handoff_sha256"]),
        (HERE / "source_handoff22.json", prep["build_source_handoff_sha256"])]
    expected = {}
    for path, expected_sha in fixed_controls:
        need(sha(path) == expected_sha, "SOURCE_HANDOFF_OR_SNAPSHOT_CHANGED")
        for row in read(path)["bindings"]:
            row_key = key(Path(row["path"]))
            if row_key in expected:
                need((expected[row_key]["sha256"], expected[row_key]["bytes"]) ==
                     (row["sha256"], row["bytes"]), "FROZEN_BINDING_CONFLICT")
            expected[row_key] = row
    review = Path(gate["independent_build_source_review_path"])
    loader = Path(gate["compiler_loader_closure_review_path"])
    paths = set(expected) | {key(p) for p in (review, loader)} | {key(p) for p, h in fixed_controls}
    need(set(by_path) == paths, "BUILD_EXACT_BINDING_SET_MISMATCH")
    for row_key, frozen in expected.items():
        actual = by_path[row_key]
        need((actual["sha256"], actual["bytes"]) == (frozen["sha256"], frozen["bytes"]), "BUILD_FROZEN_BYTES_MISMATCH")
        need(not frozen.get("capture", False) or actual.get("capture", False), "CAPTURE_OMITTED")
    for row in rows:
        check_binding(row)
    need(sha(review) == gate["independent_build_source_review_sha256"] and
         sha(loader) == gate["compiler_loader_closure_review_sha256"], "REVIEW_CHANGED")
    loader_data = read(loader)
    need(loader_data.get("status") == "COMPILER_LOADER_CLOSURE_REVIEWED_WITH_WINDOWS_TRUST_BASE" and
         loader_data.get("compiler_sha256") == sha(GXX) and loader_data.get("all_non_OS_imports_bound") is True,
         "COMPILER_LOADER_CLOSURE_OPEN")
    plan = read(NATIVE / "build_plan22.json")
    need(key(Path(plan["compiler"])) == key(GXX) and plan["source_sha256"] ==
        [sha(NATIVE / "producer_dit22.cpp"), sha(NATIVE / "checker_dif22.cpp")], "BUILD_PLAN_SOURCE_MISMATCH")
    args = []
    for tag in ("producer_dit22", "checker_dif22"):
        args.append(["-std=c++17", "-O2", "-static", "-static-libgcc", "-static-libstdc++",
            "-Wl,--no-insert-timestamp", "-I", "C:/msys64/ucrt64/include",
            str(NATIVE / (tag + ".cpp")).replace("\\", "/"), "-L", "C:/msys64/ucrt64/lib",
            "-lgmp", "-o", str(OUT / (tag + ".exe")).replace("\\", "/")])
    need(plan["commands"] == args, "FIXED_COMPILER_ARGUMENTS_MISMATCH")
    controls = {key(p): (p, h) for p, h in fixed_controls}
    controls.update({key(PREP): (PREP, prep_sha), key(GATE): (GATE, gate_sha),
        key(manifest): (manifest, prep["manifest_sha256"]),
        key(review): (review, gate["independent_build_source_review_sha256"]),
        key(loader): (loader, gate["compiler_loader_closure_review_sha256"])})
    for row in rows:
        if row.get("capture", False):
            p = Path(row["path"])
            if key(p) in controls:
                need(controls[key(p)][1] == row["sha256"], "CAPTURE_CONTROL_HASH_CONFLICT")
            controls[key(p)] = (p, row["sha256"])
    need(not ACTUAL.exists() and not OUT.exists() and not BUILD_RECEIPT.exists(), "BUILD_ALREADY_ATTEMPTED")
    return rows, controls, args, archives(), prep_sha


def main():
    global OWNED
    rows, controls, args, archive_state, prep_sha = preflight()
    ACTUAL.mkdir()
    OWNED = True
    (ACTUAL / "tmp").mkdir()
    (ACTUAL / "PREEXEC").mkdir()
    OUT.mkdir()
    writer, captures, copied, results, error = Writer(), [], 0, [], None
    try:
        for i, (original, expected_sha) in enumerate(controls.values()):
            need(sha(original) == expected_sha, "PRE_ORIGINAL_CHANGED")
            copied += original.stat().st_size
            need(copied <= 33554432, "PRE_COPY_BYTE_LIMIT")
            copy = ACTUAL / "PREEXEC" / (str(i).zfill(3) + "_" + original.name)
            shutil.copyfile(original, copy)
            need(sha(copy) == expected_sha, "PRE_COPY_CHANGED")
            captures.append({"original": str(original), "copy": str(copy), "sha256": expected_sha})
        writer.record("PRE.json", {"utc": utc(), "captures": captures, "archives": archive_state,
            "binding_count": len(rows), "scope": FIXED["scope"], "produced_binary_invocations": 0})
        spec = importlib.util.spec_from_file_location("build_windows_job22", HERE / "windows_build_job22.py")
        backend = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(backend)
        for index, arguments in enumerate(args):
            tag = "producer_build" if index == 0 else "checker_build"
            writer.open_logs(tag)
            writer.record(tag + "_START_REQUEST.json", {"utc": utc(), "compiler": str(GXX),
                "arguments": arguments, "ordinal": index + 1, "produced_binary_invocations": 0})
            result = backend.run_child(GXX, arguments, ACTUAL, ENTERED + 300,
                2147483648, 2147483648, lambda channel, data, t=tag: writer.pipe(t, channel, data),
                output_guard,
                lambda pid, t=tag: writer.record(t + "_CREATED_SUSPENDED.json", {"utc": utc(), "pid": pid}),
                lambda pid, t=tag: writer.record(t + "_START.json", {"utc": utc(), "pid": pid, "job_quotas_read_back": True}))
            result.update({"utc_FIN": utc(), "tag": tag})
            writer.record(tag + "_FIN.json", result)
            results.append(result)
            need(result["exit_code"] == 0 and result["api_or_control_error"] is None and
                result["termination_reason"] is None and result["wait_signalled"] and
                result["job_empty_confirmed"] and not result["pipe_faults"], "STOP_FIRST_BUILD_FAIL")
            binary = Path(arguments[-1])
            need(binary.is_file() and 0 < binary.stat().st_size <= 67108864, "COMPILED_FILE_MISSING_OR_OVERSIZE")
            with binary.open("rb") as f:
                need(f.read(2) == b"MZ", "OUTPUT_IMAGE_HEADER_MISSING")
            result["binary_sha256"] = sha(binary)
            output_guard()
    except BaseException as e:
        error = type(e).__name__ + ":" + str(e)
    finally:
        writer.close()
    post_error = None
    try:
        for row in rows:
            check_binding(row)
        for original, expected_sha in controls.values():
            need(sha(original) == expected_sha, "POST_ORIGINAL_CONTROL_CHANGED")
        for capture in captures:
            need(sha(Path(capture["original"])) == capture["sha256"] and
                 sha(Path(capture["copy"])) == capture["sha256"], "POST_ORIGINAL_OR_COPY_CHANGED")
        need(archives() == archive_state, "POST_ARCHIVES_CHANGED")
        output_guard()
    except BaseException as e:
        post_error = type(e).__name__ + ":" + str(e)
    success = error is None and post_error is None and len(results) == 2
    receipt = {"status": "NATIVE_BUILD_EXIT0" if success else "BUILD_STOP_NO_NUMERIC_VERDICT",
        "utc_FIN": utc(), "scope": FIXED["scope"], "preparation_sha256": prep_sha,
        "results": results, "child_exit_codes": [r["exit_code"] for r in results],
        "binary_sha256": [r.get("binary_sha256") for r in results],
        "source_sha256": [sha(NATIVE / "producer_dit22.cpp"), sha(NATIVE / "checker_dif22.cpp")],
        "build_plan_sha256": sha(NATIVE / "build_plan22.json"), "error": error,
        "post_error": post_error, "produced_binary_invocations": 0, "retry_count": 0,
        "formal_primitives": False, "coefficient_N": False, "D_N": False, "WIN": False}
    writer.record("POST.json", {"utc": utc(), "all_inputs_controls_copies_archives_intact": post_error is None,
        "post_error": post_error})
    writer.record("receipt.json", receipt)
    if success:
        with BUILD_RECEIPT.open("x", encoding="utf-8", newline="\n") as f:
            json.dump(receipt, f, ensure_ascii=False, indent=2)
            f.write("\n")
    print(receipt["status"])
    return 0 if success else 1


if __name__ == "__main__":
    def emergency_stop():
        if OWNED:
            try:
                with (ACTUAL / "WATCHDOG_TERMINATION_REQUEST.json").open("x", encoding="utf-8") as f:
                    json.dump({"utc": utc(), "status": "BUILD_HARD_WALL_POST_UNVERIFIED",
                        "produced_binary_invocations": 0, "WIN": False}, f)
            except BaseException:
                pass
        os._exit(124)

    timer = threading.Timer(max(0, ENTERED + 300 - time.monotonic()), emergency_stop)
    timer.daemon = True
    timer.start()
    try:
        raise SystemExit(main())
    except Exception as e:
        print("BUILD_PARENT_CONTROL_ERROR_NO_VERDICT", type(e).__name__, str(e), file=sys.stderr)
        raise SystemExit(2)
    finally:
        timer.cancel()
