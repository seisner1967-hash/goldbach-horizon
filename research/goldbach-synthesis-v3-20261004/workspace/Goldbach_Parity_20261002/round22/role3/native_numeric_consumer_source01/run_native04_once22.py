"""SOURCE ONLY numeric consumer of the two real BUILD04 images.

This new source has never been imported, parsed or invoked. It does not build.
ROOT numerical authorization and two independent reviews are still required.
The frozen native02 algorithms and readonly BUILD04 backend are not edited.
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
NATIVE = BASE / "round22/role4/circle_native_revision02"
BUILD = BASE / "round22/role4/circle_native_build_source04"
BUILD_ACTUAL = BUILD / "actual_build04_attempt01"
BUILD_META = BASE / "round22/role3/native_build_metadata04"
PREP = HERE / "numeric_preparation22.json"
HANDOFF = HERE / "source_handoff22.json"
PLAN = HERE / "numeric_execution_plan22.json"
POLICY = HERE / "numeric_trust_policy22.json"
GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_native_numeric04_authorization.json"
ACTUAL = HERE / "actual_numeric04_attempt01"
REVIEW = BASE / "round22/role4/native_numeric04_consumer_review_source01/source_review22.json"
TRUST_REVIEW = BASE / "round22/role4/native_numeric04_consumer_review_source01/trust_review22.json"
BACKEND = BUILD / "windows_build_job22.py"
BUILD_MANIFEST = BUILD_META / "build_manifest22.json"
BUILD_CLOSURE = BUILD_META / "build_execution_closure22_revision02.json"
BUILD_RECEIPT = NATIVE / "build_receipt04.json"
BUILD_PLAN = BUILD / "build_execution_plan22.json"
BINS = [NATIVE / "build-final04/producer_dit22.exe", NATIVE / "build-final04/checker_dif22.exe"]
CPP = [NATIVE / "producer_dit22.cpp", NATIVE / "checker_dif22.cpp"]
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PY_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
REGISTRY = BASE / "round22/previous_artifacts_sha256.json"
REG_SHA = "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99"
BACKEND_SHA = "88d857ce33eece8f90906bc5088d5cac905b868e60ede1b6439b1a3af3126cc3"
BUILD_MANIFEST_SHA = "24ea81c9ae7134f71837baed91dabc9c64f45a2438ca6223e1aedc2154a85c2f"
BUILD_CLOSURE_SHA = "dd506cebebcdbf7c75fd138d26cfb744552bdd6912e3cc37fbaa3a58fd8c0c15"
BUILD_RECEIPT_SHA = "04ce22f9ee05215ee9c7c335b41755b1da4e001a82fa20085cfe7dccca1a7fc8"
BUILD_PLAN_SHA = "538cc14faf3466bb8a0505e8f6aae3007fc84b2b6246afb2da55d37be5718156"
BUILD_PRE_SHA = "e751361aa2e9b20b7fae95b8c0fdda731338a0b7fb88c1f3aed4fb72d7ecc676"
CPP_SHA = ["bdb7b022ae20ed8dce02959b77db62ca690a9798393292db62edf262d938ed74",
           "4275ef5afc07f23c2d4b860de8f452ff1e2c07e8ab0d01686c16bdb0d09fe0eb"]
BIN_SHA = ["44d2d571a0190f7dbbb975225559d16a012693bda4197738e6311c14892cadb0",
           "2e7e095c2972fea09ee26500df9dae207ff52497d0f61f2052d76d464ebe6990"]
BIN_BYTES = [3649966, 3669445]
FIXED = {"scope": "NATIVE_NUMERIC04_FULL_N1E8_ONLY", "fixed_N": 100000000,
    "fixed_M": 100000000, "fixed_K": 134217728, "fixed_S": "288230376151711744",
    "max_children": 2, "max_retries": 0, "wall_seconds": 3600,
    "output_bytes": 2147483648, "commit_job_bytes": 2147483648,
    "rss_per_process_monitor_bytes": 2147483648, "sampled_job_rss_cap_bytes": 4294967296,
    "max_active_job_processes": 16, "max_total_job_processes": 32,
    "job_limit_flags_requested": 8968, "working_set_limit_flag_requested": False,
    "rss_os_enforced": False, "rss_control": "SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM",
    "log_bytes": 1048576, "metadata_bytes": 16777216, "capture_bytes": 33554432,
    "compiler_invocations": 0}
ENTERED = time.monotonic()
OWNED_ATTEMPT = False


def utc():
    return datetime.now(timezone.utc).isoformat()


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


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
    rows = read(REGISTRY)["sha256"]
    need(len(rows) == 3089, "ARCHIVE_COUNT_CHANGED")
    for name, digest in rows.items():
        p = (BASE / name).resolve()
        need(p.is_relative_to(BASE.resolve()) and sha(p) == digest, "ARCHIVE_CHANGED:" + name)
    return {"registry_sha256": REG_SHA, "count": 3089, "all_intact": True}


class Budget:
    def __init__(self):
        self.metadata = self.logs = 0
        self.lock = threading.Lock()
        self.log_files = {}

    def record(self, name, value):
        data = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
        need(len(data) <= 1048576, "SINGLE_METADATA_FILE_TOO_LARGE")
        with self.lock:
            need(self.metadata + len(data) <= FIXED["metadata_bytes"] - 65536, "METADATA_RESERVE_EXHAUSTED")
            with (ACTUAL / name).open("xb") as f:
                f.write(data)
            self.metadata += len(data)

    def open_logs(self, label):
        for channel in ("stdout", "stderr"):
            self.log_files[label, channel] = (ACTUAL / (label + "." + channel + ".log")).open("xb")

    def write_log(self, label, channel, data):
        with self.lock:
            room = FIXED["log_bytes"] - self.logs
            part = data[:room]
            if part:
                self.log_files[label, channel].write(part)
                self.log_files[label, channel].flush()
                self.logs += len(part)
            need(len(data) <= room, "PIPE_BYTE_CAP_EXHAUSTED")

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
        need(payload.is_dir(), "PAYLOAD_NOT_DIRECTORY")
        for p in payload.iterdir():
            need(p.is_file() and p.name in allowed and p.stat().st_size <= allowed[p.name],
                 "PAYLOAD_FORMAT_SIZE_LIMIT")
    # This is a monitor, not a filesystem quota against a hostile program.


def payload_hashes():
    payload = ACTUAL / "payload"
    need(payload.is_dir() and {p.name for p in payload.iterdir()} ==
         {"factors.bin", "records.bin", "producer.txt"}, "FINAL_PAYLOAD_PATH_SET")
    return {p.name: {"bytes": p.stat().st_size, "sha256": sha(p)} for p in payload.iterdir()}


def load_backend():
    # Only the ROOT-authorized runtime may reach this import, after all captures.
    need(sha(BACKEND) == BACKEND_SHA, "READONLY_BUILD04_BACKEND_CHANGED")
    spec = importlib.util.spec_from_file_location("readonly_build04_windows_job22", BACKEND)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def add_row(rows, path, digest, size=None, capture=False):
    p = Path(path)
    row = {"path": str(p), "sha256": digest,
           "bytes": p.stat().st_size if size is None else size, "capture": capture}
    old = rows.get(key(p))
    if old is not None:
        need((old["sha256"], old["bytes"]) == (row["sha256"], row["bytes"]), "DEPENDENCY_BINDING_CONFLICT")
        row["capture"] = capture or old.get("capture", False)
    rows[key(p)] = row


def expected_rows(handoff_sha, review_sha, trust_sha):
    # Reconstruct the dependency set from frozen historical inventories. A count
    # alone cannot allow omitted old consumers, CPP, original controls or copies.
    out = {}
    for p, digest in ((BUILD_MANIFEST, BUILD_MANIFEST_SHA), (BUILD_CLOSURE, BUILD_CLOSURE_SHA),
                      (BUILD_ACTUAL / "PRE.json", BUILD_PRE_SHA), (HANDOFF, handoff_sha)):
        need(sha(p) == digest, "FROZEN_CONTROL_CHANGED:" + str(p))
    old = read(BUILD_MANIFEST)["bindings"]
    need(len(old) == 6375, "BUILD04_MANIFEST_COUNT")
    for row in old + read(HANDOFF)["bindings"]:
        add_row(out, row["path"], row["sha256"], row["bytes"], row.get("capture", False))
    closed = read(BUILD_CLOSURE)
    need(closed.get("parent_invocations") == 1 and closed.get("parent_exit_code") == 0 and
         closed.get("compiler_processes_created") == 2 and closed.get("produced_binary_invocations") == 0,
         "NO_CLOSED_REAL_BUILD04")
    for row in closed["output_bindings"] + closed["binary_bindings"]:
        add_row(out, row["path"], row["sha256"], row["bytes"], False)
    captures = read(BUILD_ACTUAL / "PRE.json")["captures"]
    need(len(captures) == 47, "BUILD04_CAPTURE_COUNT")
    for row in captures:
        add_row(out, row["original"], row["sha256"], capture=True)
        add_row(out, row["copy"], row["sha256"], capture=False)
    for p, digest in ((BUILD_MANIFEST, BUILD_MANIFEST_SHA), (BUILD_CLOSURE, BUILD_CLOSURE_SHA),
                      (HANDOFF, handoff_sha), (REVIEW, review_sha), (TRUST_REVIEW, trust_sha)):
        add_row(out, p, digest, capture=True)
    return out


def validate_build():
    need(sha(BUILD_RECEIPT) == BUILD_RECEIPT_SHA and sha(BUILD_PLAN) == BUILD_PLAN_SHA and
         sha(BUILD_ACTUAL / "receipt.json") == BUILD_RECEIPT_SHA, "BUILD04_RECEIPT_OR_PLAN_CHANGED")
    data, plan = read(BUILD_RECEIPT), read(BUILD_PLAN)
    need(data.get("status") == "NATIVE_BUILD_EXIT0" and data.get("child_exit_codes") == [0, 0] and
         data.get("error") is None and data.get("post_error") is None, "NO_REAL_BUILD04_TWO_EXIT0")
    need(data.get("actual_build_plan_sha256") == BUILD_PLAN_SHA and
         key(Path(data["actual_build_plan_path"])) == key(BUILD_PLAN), "ACTUAL_BUILD04_PLAN_LINK")
    need(data.get("source_sha256") == CPP_SHA and data.get("binary_sha256") == BIN_SHA and
         data.get("produced_binary_invocations") == 0 and data.get("numeric_authorization") is False,
         "BUILD04_SOURCE_BINARY_OR_SCOPE_LINK")
    need(data.get("output_directory") == str(BINS[0].parent) and
         data.get("working_directory") == str(BUILD_ACTUAL), "ACTUAL_BUILD04_PATH_LINK")
    need(plan.get("backend_sha256") == BACKEND_SHA and plan.get("source_sha256") == CPP_SHA,
         "BUILD04_BACKEND_PLAN_LINK")
    need([sha(p) for p in CPP] == CPP_SHA and [sha(p) for p in BINS] == BIN_SHA and
         [p.stat().st_size for p in BINS] == BIN_BYTES, "BUILD04_FROZEN_CPP_OR_IMAGES_CHANGED")
    need({p.name for p in BINS[0].parent.iterdir()} == {p.name for p in BINS}, "BUILD_FINAL04_NOT_TWO_EXES_ONLY")


def validate_reviews(gate):
    review_sha, trust_sha = gate["independent_numeric_source_review_sha256"], gate["numeric_trust_review_sha256"]
    need(key(Path(gate["independent_numeric_source_review_path"])) == key(REVIEW) and
         key(Path(gate["numeric_trust_review_path"])) == key(TRUST_REVIEW), "FIXED_REVIEW_PATHS_REQUIRED")
    need(sha(REVIEW) == review_sha and sha(TRUST_REVIEW) == trust_sha, "NUMERIC_REVIEWS_CHANGED")
    review, trust = read(REVIEW), read(TRUST_REVIEW)
    need(review.get("status") == "NUMERIC04_SOURCE_REVIEW_CLOSED_WITH_NATIVE_REFINEMENT_OPEN" and
         review.get("scope") == FIXED["scope"] and review.get("unresolved_execution_blockers") == [] and
         review.get("reviewer") == "ROLE4" and review.get("source_handoff_sha256") == sha(HANDOFF) and
         review.get("parent_sha256") == sha(Path(__file__)) and review.get("backend_sha256") == BACKEND_SHA,
         "NUMERIC_SOURCE_REVIEW_STILL_OPEN")
    need(sha(POLICY) == gate["numeric_trust_policy_sha256"] and
         gate.get("accept_installed_Windows_and_frozen_native_runtime_trust") is True,
         "NO_EXPLICIT_ROOT_NUMERIC_TRUST_ACKNOWLEDGMENT")
    need(trust.get("status") == "NUMERIC04_FIXED_IMAGES_REVIEWED_WITH_EXPLICIT_WINDOWS_NATIVE_TRUST" and
         trust.get("scope") == FIXED["scope"] and trust.get("reviewer") == "ROLE4" and
         trust.get("binary_sha256") == BIN_SHA and trust.get("source_sha256") == CPP_SHA and
         trust.get("backend_sha256") == BACKEND_SHA and trust.get("policy_sha256") == sha(POLICY) and
         trust.get("installed_Windows_and_frozen_native_runtime_trusted") is True and
         trust.get("effective_loads_observed") is False and
         trust.get("universal_loader_closure_verified") is False and
         trust.get("all_non_OS_imports_bound") is False and
         trust.get("numeric_authorization") is False and trust.get("produced_binary_invocations") == 0 and
         trust.get("unresolved_execution_blockers") == [], "NUMERIC_TRUST_REVIEW_STILL_OPEN")
    for name in ("job_limit_flags_requested", "working_set_limit_flag_requested", "rss_os_enforced", "rss_control"):
        need(review.get(name) == FIXED[name] and trust.get(name) == FIXED[name], "REVIEW_RESOURCE_MISMATCH:" + name)
    return review_sha, trust_sha


def preflight():
    global OWNED_ATTEMPT
    need(key(Path(sys.executable)) == key(PYTHON) and sha(PYTHON) == PY_SHA, "CANONICAL_PYTHON_REQUIRED")
    need(key(Path.cwd()) == key(HERE), "FIXED_NUMERIC_PARENT_WORKDIR_REQUIRED")
    need(sys.flags.isolated == 1 and sys.flags.no_site == 1 and sys.flags.dont_write_bytecode == 1 and
         sys.flags.utf8_mode == 1, "CANONICAL_ISOLATED_FLAGS_REQUIRED")
    prep_sha, gate_sha = sha(PREP), sha(GATE)
    prep, gate = read(PREP), read(GATE)
    need(prep.get("status") == "NATIVE_NUMERIC04_METADATA_PREPARED" and
         gate.get("status") == "AUTHORIZED" and gate.get("preparation_sha256") == prep_sha,
         "NO_DISTINCT_EXACT_ROOT_NUMERIC_GATE")
    for name, value in FIXED.items():
        need(type(prep.get(name)) is type(value) and type(gate.get(name)) is type(value) and
             prep.get(name) == value and gate.get(name) == value, "FIXED_GATE_RESOURCE_MISMATCH:" + name)
    need(prep.get("build_receipt_sha256") == BUILD_RECEIPT_SHA and prep.get("actual_build_plan_sha256") == BUILD_PLAN_SHA and
         gate.get("build_receipt_sha256") == BUILD_RECEIPT_SHA and gate.get("binary_sha256") == BIN_SHA,
         "PREPARATION_GATE_BUILD04_LINK")
    need(sha(PLAN) == prep["numeric_execution_plan_sha256"] == gate["numeric_execution_plan_sha256"] and
         sha(HANDOFF) == prep["source_handoff_sha256"] == gate["source_handoff_sha256"], "NUMERIC_SOURCE_PLAN_CHANGED")
    manifest = HERE / "numeric_manifest22.json"
    need(key(Path(prep["manifest_path"])) == key(manifest) and
         sha(manifest) == prep["manifest_sha256"] == gate["manifest_sha256"], "NUMERIC_MANIFEST_CHANGED")
    validate_build()
    review_sha, trust_sha = validate_reviews(gate)
    rows = read(manifest)["bindings"]
    actual = {key(Path(row["path"])): row for row in rows}
    expected = expected_rows(prep["source_handoff_sha256"], review_sha, trust_sha)
    need(len(rows) == len(actual) == len(expected) == prep["binding_count"] and set(actual) == set(expected),
         "EXACT_NUMERIC_BINDING_PATH_SET_MISMATCH")
    for path_key, row in expected.items():
        observed = actual[path_key]
        need((observed["sha256"], observed["bytes"]) == (row["sha256"], row["bytes"]), "BINDING_EXPECTATION_CHANGED")
        need(not row.get("capture", False) or observed.get("capture", False), "REQUIRED_CAPTURE_OMITTED")
    for row in rows:
        binding(row)
    controls = {key(p): (p, digest) for p, digest in ((PREP, prep_sha), (GATE, gate_sha),
        (manifest, prep["manifest_sha256"]), (REVIEW, review_sha), (TRUST_REVIEW, trust_sha))}
    for row in rows:
        if row.get("capture", False):
            p = Path(row["path"])
            if key(p) in controls:
                need(controls[key(p)][1] == row["sha256"], "CONFLICTING_CAPTURE_EXPECTATION")
            controls[key(p)] = (p, row["sha256"])
    archived = archives()
    need(not ACTUAL.exists(), "UNIQUE_NUMERIC_ATTEMPT_ALREADY_EXISTS")
    ACTUAL.mkdir()
    OWNED_ATTEMPT = True
    (ACTUAL / "tmp").mkdir()
    (ACTUAL / "PREEXEC").mkdir()
    captures, copied = [], 0
    try:
        for index, (p, digest) in enumerate(controls.values()):
            need(sha(p) == digest, "PRE_CAPTURE_ORIGINAL_CHANGED")
            copied += p.stat().st_size
            need(copied <= FIXED["capture_bytes"], "PRE_CAPTURE_BYTES_LIMIT")
            dst = ACTUAL / "PREEXEC" / (str(index).zfill(3) + "_" + p.name)
            shutil.copyfile(p, dst)
            need(sha(dst) == digest, "PRE_CAPTURE_COPY_CHANGED")
            captures.append({"original": str(p), "copy": str(dst), "sha256": digest})
    except BaseException as error:
        with (ACTUAL / "PRE_CONTROL_FAILURE.json").open("x", encoding="utf-8") as f:
            json.dump({"utc": utc(), "status": "METADATA_FAILURE_NO_NATIVE_CHILD", "failure": repr(error),
                       "retry_count": 0, "native_Lean_refinement": False, "D_N": False, "WIN": False}, f)
        raise
    return prep_sha, gate_sha, rows, controls, captures, archived


def decimal(value, digits=47):
    need(1 <= len(value) <= digits and value.isascii() and value.isdecimal() and
         (len(value) == 1 or value[0] != "0"), "NONCANONICAL_RESULT_INTEGER")
    return int(value)


def interpret_checker_output():
    # No floating point, no new primitive evaluation. Read only the final fixed
    # native text and construct the rational envelope specified in the contract.
    raw = (ACTUAL / "checker.stdout.log").read_bytes()
    need(len(raw) <= 4096, "CHECKER_RESULT_SIZE")
    lines = raw.decode("ascii").replace("\r\n", "\n").splitlines()
    need(len(lines) == 9 and lines[0] == "EXACT_INTEGER_PROJECTION_CHECKED_PENDING_PRIMITIVE_PROOF" and
         lines[5:] == ["FORMAL_PRIMITIVES false", "SPECTRAL_H1 false", "D_N false", "WIN false"],
         "CHECKER_SUCCESS_RECORD_MISSING")
    values = []
    for line, label in zip(lines[1:5], ("C_A", "C_B", "ERROR_NUMERATOR", "ERROR_DENOMINATOR")):
        parts = line.split(" ")
        need(len(parts) == 2 and parts[0] == label, "CHECKER_RESULT_SCHEMA")
        values.append(decimal(parts[1]))
    ca, cb, joint_num, den = values
    scale = int(FIXED["fixed_S"])
    primary_num = (FIXED["fixed_N"] + 1) * (64 * scale + 1)
    need(joint_num == 2 * primary_num and den == scale * scale and
         abs(ca - cb) <= joint_num and joint_num * 1000000 <= den and
         ca < (1 << 153) and cb < (1 << 153), "EXACT_RESULT_ENVELOPE_GUARD")
    producer = (ACTUAL / "payload/producer.txt").read_text(encoding="ascii").split()
    need(len(producer) == 11 and producer[:4] == ["ROUND22_NATIVE_DIT_OUTPUT", "100000000", "134217728",
         "288230376151711744"] and producer[-1] == "NO_INDEPENDENT_CHECKER_VERDICT" and
         decimal(producer[-2]) == ca, "PRODUCER_CHECKER_FINAL_INTEGER_LINK")
    residues = [decimal(x, 10) for x in producer[4:9]]
    primes = [2013265921, 2281701377, 3221225473, 3489660929, 3892314113]
    need(all(r < p and ca % p == r for r, p in zip(residues, primes)), "PARENT_RESIDUE_LINK")
    return {"C_A_integer": str(ca), "C_B_integer": str(cb), "modular_residues": residues,
        "coefficient_denominator": str(den), "primary_radius_numerator": str(primary_num),
        "joint_reference_radius_numerator": str(joint_num), "joint_radius_le_1e_minus6": True,
        "declared_primary_interval_numerators": [str(ca - primary_num), str(ca + primary_num)],
        "declared_B40_interval_numerators": [str(cb - primary_num), str(cb + primary_num)],
        "interval_link_level": "PAPER_AUDITED_PENDING_NATIVE_CATALOGUE_AND_MACHINE_REFINEMENT",
        "B40_real_log_refinement_Lean": False, "native_Lean_refinement": False,
        "spectral_H1": False, "D_N": False, "WIN": False,
        "mutant_runs": 0, "mutants_discriminated_by_this_attempt": False}


def main():
    prep_sha, gate_sha, rows, controls, captures, archived = preflight()
    budget, results, failure, interpreted = Budget(), [], None, None
    process_events = {"created": 0, "resumed": 0}
    budget.record("PRE.json", {"utc": utc(), "preparation_sha256": prep_sha, "gate_sha256": gate_sha,
        "binding_count": len(rows), "captures": captures, "archives": archived,
        "build_receipt_sha256": BUILD_RECEIPT_SHA, "binary_sha256": BIN_SHA,
        "numeric_parent_invocations": 1, "compiler_invocations": 0, "native_Lean_refinement": False,
        "D_N": False, "WIN": False})
    try:
        backend = load_backend()
        deadline = ENTERED + FIXED["wall_seconds"]
        for label, exe in zip(("producer", "checker"), BINS):
            need(time.monotonic() < deadline, "SHARED_WALL_BUDGET_EXHAUSTED")
            need(sha(exe) == BIN_SHA[len(results)], "IMAGE_CHANGED_BEFORE_CHILD")
            budget.open_logs(label)
            budget.record(label + "_START_REQUEST.json", {"utc": utc(), "executable": str(exe),
                "sha256": sha(exe), "arguments": [str(ACTUAL / "payload")], "cwd": str(ACTUAL),
                "ordinal": len(results) + 1, "max_children": 2, "retry_count": 0,
                "created": False, "resumed": False, "limits": FIXED})

            def created(pid, tag=label):
                process_events["created"] += 1
                budget.record(tag + "_CREATED_SUSPENDED.json", {"utc": utc(), "pid": pid,
                    "resumed": False, "before_job_assignment": True})

            def resumed(pid, tag=label):
                process_events["resumed"] += 1
                budget.record(tag + "_START.json", {"utc": utc(), "pid": pid, "job_assigned": True,
                    "job_commit_active_kill_limits_read_back": True, "job_limit_flags_requested": 8968,
                    "working_set_limit_flag_requested": False, "rss_os_enforced": False,
                    "rss_control": FIXED["rss_control"]})

            result = backend.run_child(exe, [str(ACTUAL / "payload")], ACTUAL, deadline,
                FIXED["commit_job_bytes"], FIXED["rss_per_process_monitor_bytes"],
                lambda channel, data, tag=label: budget.write_log(tag, channel, data),
                output_guard, created, resumed)
            result["utc_FIN"], result["label"] = utc(), label
            budget.record(label + "_FIN.json", result)
            results.append(result)
            output_guard()
            need(result["created_suspended"] and result["resumed"] and result["exit_code"] == 0 and
                 result["termination_reason"] is None and result["wait_signalled"] and result["job_empty_confirmed"] and
                 result["api_or_control_error"] is None and not result["pipe_faults"], "STOP_FIRST_FAIL:" + label)
            for field in ("job_limit_flags_requested", "working_set_limit_flag_requested", "rss_os_enforced", "rss_control",
                          "max_active_job_processes", "max_total_job_processes", "sampled_job_rss_cap_bytes"):
                need(result[field] == FIXED[field], "BACKEND_RESULT_LIMIT_MISMATCH:" + field)
            if label == "producer":
                payload_before = payload_hashes()
                budget.record("producer_payload_hashes.json", payload_before)
        need(payload_hashes() == payload_before, "CHECKER_CHANGED_PRODUCER_PAYLOAD")
    except BaseException as error:
        failure = type(error).__name__ + ":" + str(error)
    finally:
        budget.close_logs()
    if failure is None:
        try:
            interpreted = interpret_checker_output()
        except BaseException as error:
            failure = type(error).__name__ + ":" + str(error)
    conservation_error = None
    try:
        for row in rows:
            binding(row)
        for p, digest in controls.values():
            need(sha(p) == digest, "POST_CONTROL_ORIGINAL_CHANGED")
        for row in captures:
            need(sha(Path(row["original"])) == row["sha256"] and sha(Path(row["copy"])) == row["sha256"],
                 "POST_CAPTURE_ORIGINAL_OR_COPY_CHANGED")
        need(archives() == archived, "POST_ARCHIVE_CHANGED")
        output_guard()
    except BaseException as error:
        conservation_error = type(error).__name__ + ":" + str(error)
    success = failure is None and conservation_error is None and len(results) == 2 and interpreted is not None
    status = ("PAPER_AUDITED_EXACT_INTEGER_PROJECTION_AUX_CHECKED_PENDING_NATIVE_REFINEMENT" if success
              else "NATIVE_NUMERIC_STOP_NO_MATHEMATICAL_VERDICT")
    budget.record("POST.json", {"utc": utc(), "conservation_error": conservation_error,
        "all_bindings_controls_originals_copies_archives_intact": conservation_error is None})
    if success:
        budget.record("coefficient_result.json", interpreted)
    budget.record("receipt.json", {"status": status, "utc_FIN": utc(), "scope": FIXED["scope"],
        "preparation_sha256": prep_sha, "gate_sha256": gate_sha, "parent_invocations": 1, "retry_count": 0,
        "children_returned": len(results), "produced_binary_processes_created": process_events["created"],
        "produced_binary_processes_resumed": process_events["resumed"], "results": results,
        "failure": failure, "conservation_error": conservation_error, "elapsed_parent_seconds": time.monotonic() - ENTERED,
        "limits": FIXED, "binary_sha256": BIN_SHA, "build_receipt_sha256": BUILD_RECEIPT_SHA,
        "coefficient_result_present": (ACTUAL / "coefficient_result.json").is_file(), "compiler_invocations": 0,
        "native_Lean_refinement": False, "B40_real_log_refinement_Lean": False,
        "effective_loads_observed": False, "universal_loader_closure_verified": False,
        "mutant_runs": 0, "spectral_H1": False, "D_N": False, "WIN": False})
    print(status)
    return 0 if success else 1


if __name__ == "__main__":
    def emergency_stop():
        if OWNED_ATTEMPT:
            try:
                with (ACTUAL / "WATCHDOG_TERMINATION_REQUEST.json").open("x", encoding="utf-8") as f:
                    json.dump({"utc": utc(), "status": "HARD_WALL_NO_VERDICT_POST_UNVERIFIED",
                        "wall_seconds": 3600, "conservation_verified": False,
                        "native_Lean_refinement": False, "D_N": False, "WIN": False}, f)
            except BaseException:
                pass
        os._exit(124)  # closes inherited Job handles; KILL_ON_JOB_CLOSE remains.

    watchdog = threading.Timer(max(0, ENTERED + FIXED["wall_seconds"] - time.monotonic()), emergency_stop)
    watchdog.daemon = True
    watchdog.start()
    try:
        raise SystemExit(main())
    except Exception as error:
        print("NATIVE_NUMERIC_PARENT_CONTROL_ERROR_NO_VERDICT", type(error).__name__, str(error), file=sys.stderr)
        raise SystemExit(2)
    finally:
        watchdog.cancel()
