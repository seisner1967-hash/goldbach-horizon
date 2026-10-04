"""Operational N=10^8 launcher, exact receipts and Windows resource monitoring."""
import argparse
import ctypes
from ctypes import wintypes
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SCALE = 288230376151711744
PRIMES = [2013265921, 2281701377, 3221225473, 3489660929, 3892314113]
INPUTS = {
    "factors.bin": (400000020, "32450e19fb3d9d8a567cf03e262ddb4f46f44014da606ed5e27b69cb90c1baa2"),
    "records.bin": (92183304, "bf6bfeb2d8431326cf677df7605bac3d12caa189f22a87e7e4267aff6a093b6d"),
    "producer.txt": (194, "aeee44e0e6cdc503504d9ea3329ab6b83b3a665462472318265932200ab04383"),
}


def utc():
    return datetime.now(timezone.utc).isoformat()


def emit(event, **fields):
    print(json.dumps({"utc": utc(), "event": event, **fields}), flush=True)


def record(directory, name, value):
    with (directory / name).open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def payload_bindings(directory):
    rows = {}
    for name, (size, digest) in INPUTS.items():
        path = directory / name
        require(path.is_file() and path.stat().st_size == size, "PAYLOAD_SIZE_MISMATCH:" + name)
        actual = sha256(path)
        require(actual == digest, "PAYLOAD_SHA256_MISMATCH:" + name)
        rows[name] = {"path": str(path), "bytes": size, "sha256": actual}
    return rows


def hardware():
    class MemoryStatus(ctypes.Structure):
        _fields_ = [("length", wintypes.DWORD), ("load", wintypes.DWORD)] + [
            (name, ctypes.c_ulonglong) for name in ("total_physical", "available_physical",
                "total_pagefile", "available_pagefile", "total_virtual", "available_virtual", "extended_virtual")]

    status = MemoryStatus()
    status.length = ctypes.sizeof(status)
    kernel = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel.GlobalMemoryStatusEx.argtypes = [ctypes.POINTER(MemoryStatus)]
    kernel.GlobalMemoryStatusEx.restype = wintypes.BOOL
    require(kernel.GlobalMemoryStatusEx(ctypes.byref(status)), "GlobalMemoryStatusEx_FAILED")
    return {"logical_processors": os.cpu_count(), "physical_memory_bytes": status.total_physical,
        "available_physical_bytes": status.available_physical, "memory_load_percent": status.load,
        "available_commit_bytes": status.available_pagefile}


def interpret(stdout_path, payload):
    raw = stdout_path.read_bytes()
    require(len(raw) <= 4096, "CHECKER_OUTPUT_SIZE")
    lines = raw.decode("ascii").splitlines()
    require(len(lines) == 12 and lines[0] == "EXACT_INTEGER_PROJECTION_CHECKED_PENDING_PRIMITIVE_PROOF",
        "CHECKER_SUCCESS_RECORD_MISSING")
    expected = {"C_A", "DIRECT_A", "C_B", "ERROR_NUMERATOR", "ERROR_DENOMINATOR",
        "RECORD_COUNT", "RESIDUES", "FORMAL_PRIMITIVES", "SPECTRAL_H1", "D_N", "WIN"}
    fields = {}
    for line in lines[1:]:
        parts = line.split(" ", 1)
        require(len(parts) == 2 and parts[0] in expected and parts[0] not in fields,
            "CHECKER_RECORD_SCHEMA")
        fields[parts[0]] = parts[1]
    require(set(fields) == expected and all(fields[label] == "false" for label in
        ("FORMAL_PRIMITIVES", "SPECTRAL_H1", "D_N", "WIN")), "CHECKER_MARKER_SCHEMA")
    numeric_labels = ("C_A", "DIRECT_A", "C_B", "ERROR_NUMERATOR", "ERROR_DENOMINATOR", "RECORD_COUNT")
    require(all(fields[label].isascii() and fields[label].isdigit() for label in numeric_labels),
        "CHECKER_DECIMAL_SCHEMA")
    ca, direct_a, cb, joint, denominator, records = (int(fields[label]) for label in numeric_labels)
    require(direct_a == ca and records == 5761455, "CANONICAL_DIRECT_A32_OR_RECORD_COUNT")
    checker_residues = fields["RESIDUES"].split(" ")
    require(len(checker_residues) == 5 and all(value.isascii() and value.isdigit()
        for value in checker_residues), "CHECKER_RESIDUE_SCHEMA")
    checker_residues = [int(value) for value in checker_residues]
    primary = 100000001 * (64 * SCALE + 1)
    require(joint == 2 * primary and denominator == SCALE * SCALE,
        "EXACT_ERROR_BUDGET_SCHEMA")
    require(abs(ca - cb) <= joint and joint * 1000000 <= denominator,
        "EXACT_ERROR_BUDGET_EXCEEDED")
    require(0 <= ca < (1 << 153) and 0 <= cb < (1 << 153), "COEFFICIENT_RANGE")
    producer = (payload / "producer.txt").read_text(encoding="ascii").split()
    require(len(producer) == 11 and producer[:4] == ["ROUND22_NATIVE_DIT_OUTPUT", "100000000",
        "134217728", str(SCALE)] and producer[-1] == "NO_INDEPENDENT_CHECKER_VERDICT"
        and int(producer[-2]) == ca, "PRODUCER_CHECKER_COEFFICIENT_DISAGREEMENT")
    residues = [int(value) for value in producer[4:9]]
    require(residues == checker_residues, "PRODUCER_CHECKER_RESIDUE_DISAGREEMENT")
    require(all(0 <= r < p and ca % p == r for r, p in zip(residues, PRIMES)),
        "PARENT_CRT_RESIDUE_CHECK_FAILED")
    return {"N": 100000000, "K": 134217728, "S": str(SCALE), "C_A": str(ca),
        "C_B": str(cb), "DIRECT_A": str(direct_a), "record_count": records,
        "exact_CRT_and_direct_A32_equality": True,
        "modular_residues": residues, "absolute_integer_gap": str(abs(ca - cb)),
        "coefficient_denominator": str(denominator), "primary_error_numerator": str(primary),
        "joint_error_numerator": str(joint), "joint_error_le_1e_minus6": True,
        "canonical_A32_validated_by_native_checker": True,
        "native_Lean_refinement": False, "spectral_H1": False, "D_N": False, "WIN": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    programs = parser.add_mutually_exclusive_group()
    programs.add_argument("--checker", type=Path)
    programs.add_argument("--producer", type=Path)
    parser.add_argument("--payload", type=Path, default=ROOT / "Goldbach_Parity_20261002/round22/role3"
        "/native_numeric_consumer_source01/actual_numeric04_attempt01/payload")
    parser.add_argument("--run-directory", type=Path, default=HERE / ("run_" +
        datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")))
    parser.add_argument("--max-wall-seconds", type=float, default=86400)
    parser.add_argument("--commit-gib", type=float, default=3)
    parser.add_argument("--progress-seconds", type=float, default=30)
    args = parser.parse_args()
    require(os.name == "nt", "WINDOWS_REQUIRED")
    require(args.max_wall_seconds > 0 and args.commit_gib > 0 and args.progress_seconds > 0,
        "POSITIVE_RESOURCE_LIMITS_REQUIRED")
    label = "producer" if args.producer else "checker"
    program = args.producer or args.checker or HERE / "checker_dif22_operational.exe"
    checker, original, run = (p.resolve() for p in (program, args.payload, args.run_directory))
    require(checker.is_file(), "NATIVE_PROGRAM_MISSING")
    if label == "producer":
        require(not original.exists() and original.parent.is_dir(), "FRESH_PRODUCER_PAYLOAD_REQUIRED")
    run.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    status, error, child = "NO_NUMERICAL_VERDICT", None, None
    original_pre = copied_pre = None
    try:
        host = hardware()
        commit_cap = int(args.commit_gib * (1 << 30))
        require(host["available_commit_bytes"] > commit_cap, "INSUFFICIENT_AVAILABLE_COMMIT")
        emit("preflight", run_directory=str(run), checker=str(checker), hardware=host)
        payload = original if label == "producer" else run / "payload"
        if label == "checker":
            original_pre = payload_bindings(original)
            payload.mkdir()
            for name in INPUTS:
                shutil.copyfile(original / name, payload / name)
            copied_pre = payload_bindings(payload)
        (run / "tmp").mkdir()
        backend_path = HERE / "infrastructure/windows_numeric_job.py"
        record(run, "PRE.json", {"utc": utc(), "checker": str(checker), "checker_sha256": sha256(checker),
            "backend_sha256": sha256(backend_path), "hardware": host, "payload_original": original_pre,
            "payload_copy": copied_pre, "commit_cap_bytes": commit_cap,
            "max_wall_seconds": args.max_wall_seconds, "working_set_limit_requested": False,
            "retry_count": 0, "label": label, "fresh_producer_invocation": label == "producer"})
        spec = importlib.util.spec_from_file_location("numerical_windows_job", backend_path)
        backend = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(backend)
        with ((run / (label + ".stdout.log")).open("xb") as out,
                (run / (label + ".stderr.log")).open("xb") as err,
                (run / "progress.jsonl").open("x", encoding="utf-8") as progress_log):
            streams, written = {"stdout": out, "stderr": err}, {"stdout": 0, "stderr": 0}

            def writer(channel, data):
                written[channel] += len(data)
                require(written[channel] <= 1048576, "NATIVE_LOG_BYTE_LIMIT")
                streams[channel].write(data)
                streams[channel].flush()

            def progress(sample):
                sample.update(utc=utc(), event="native_progress", label=label)
                progress_log.write(json.dumps(sample) + "\n")
                progress_log.flush()
                print(json.dumps(sample), flush=True)

            def created(pid):
                record(run, label + "_CREATED_SUSPENDED.json", {"utc": utc(), "pid": pid})
                emit("child_created_suspended", pid=pid, label=label)

            def resumed(pid):
                record(run, label + "_START.json", {"utc": utc(), "pid": pid, "job_assigned": True})
                emit("child_resumed", pid=pid, label=label)

            child = backend.run_child(checker, [str(payload)], run, started + args.max_wall_seconds,
                commit_cap, commit_cap, writer, lambda: None, created, resumed, progress,
                args.progress_seconds)
        record(run, label + "_FIN.json", {"utc": utc(), **child})
        require(child["exit_code"] == 0 and child["wait_signalled"] and child["job_empty_confirmed"]
            and child["termination_reason"] is None and child["api_or_control_error"] is None
            and not child["pipe_faults"], "NATIVE_CHILD_DID_NOT_COMPLETE_SUCCESSFULLY")
        if label == "checker":
            result = interpret(run / "checker.stdout.log", payload)
            record(run, "coefficient_result.json", result)
            status = "NUMERICAL_CRT_DIRECT_A32_AND_ERROR_BUDGET_VALIDATED"
        else:
            copied_pre = payload_bindings(payload)
            status = "FRESH_PRODUCER_EXIT0_EXPECTED_PAYLOAD_BYTES"
    except BaseException as failure:
        error = type(failure).__name__ + ":" + str(failure)
    conservation = False
    try:
        if label == "producer" and copied_pre is not None:
            copied_post = payload_bindings(payload)
            conservation = copied_post == copied_pre
            require(conservation, "PAYLOAD_POST_CHANGED")
            record(run, "POST.json", {"utc": utc(), "fresh_payload": copied_post,
                "matches_archived_producer_payload_sha256": True, "input_bytes_conserved": conservation})
        elif original_pre is not None and copied_pre is not None:
            original_post = payload_bindings(original)
            copied_post = payload_bindings(run / "payload")
            conservation = original_post == original_pre and copied_post == copied_pre
            require(conservation, "PAYLOAD_POST_CHANGED")
            record(run, "POST.json", {"utc": utc(), "payload_original": original_post,
                "payload_copy": copied_post, "input_bytes_conserved": conservation})
    except BaseException as failure:
        error = (error + ";" if error else "") + type(failure).__name__ + ":" + str(failure)
    if error or not conservation:
        status = "NO_NUMERICAL_VERDICT"
    receipt = {"utc": utc(), "status": status, "error": error, "wall_seconds": time.monotonic() - started,
        "child": child, "label": label, "input_bytes_conserved": conservation,
        "run_directory": str(run), "payload_directory": str(payload) if "payload" in locals() else None,
        "D_N": False, "WIN": False}
    record(run, "receipt.json", receipt)
    emit("parent_FIN", **receipt)
    return 0 if error is None and conservation else 1


if __name__ == "__main__":
    raise SystemExit(main())
