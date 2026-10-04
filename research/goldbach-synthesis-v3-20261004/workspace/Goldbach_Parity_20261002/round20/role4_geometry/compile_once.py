"""Prepared launcher v2: a distinct root geometry gate is mandatory before Lean.

Targets only the new geometry source. Existing PASS modules are read-only imports.
This launcher has not been executed during geometry preparation.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
B = W.parents[1]
SRC = W / "FriableSourceGeometry.lean"
PREP = W / "preparation_v2.json"
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ["aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib",
            "plausible", "proofwidgets", "Qq"]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def write_new(p, data):
    with p.open("x", encoding="utf-8") as h:
        h.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


if len(sys.argv) != 2:
    raise SystemExit("Require the distinct root geometry gate path; no implicit gate")
gate_path = Path(sys.argv[1]).resolve()
gate = json.loads(gate_path.read_text(encoding="utf-8"))
prep = json.loads(PREP.read_text(encoding="utf-8"))
assert gate["authorization"] == "ROOT20_GEOMETRY_COMPILE"
assert gate["root_authorized"] is True
assert gate["round"] == 20 and gate["node"] == "14.5"
assert gate["full_geometry_source_read"] is True
assert gate["full_geometry_launcher_read"] is True
assert gate["full_geometry_preparation_read"] is True
assert gate["canonical_new_numeric_pass_inspected"] is True
assert gate["allow_repairs_only_after_actual_failed_attempt"] is True
assert gate["initial_reviewed_source_sha256"] == prep["source_sha256"]
assert gate["launcher_sha256"] == prep["launcher_sha256"] == sha(Path(__file__))
assert gate["preparation_sha256"] == sha(PREP)
assert gate["report_sha256"] == prep["report_sha256"] == sha(B / "round20" / "agent4_geometry_preparation.md")
assert gate["protocol_revision_sha256"] == prep["protocol_revision_sha256"] == sha(W / "protocol_revision02.md")
assert sha(LEAN) == prep["compiler_sha256"]
PYTHON = Path(sys.executable).resolve()
assert PYTHON == Path(prep["python_runtime"]).resolve()
assert sha(PYTHON) == prep["python_runtime_sha256"]

manifest_path = W / "inputs_sha256.json"
assert sha(manifest_path) == prep["inputs_manifest_sha256"]
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
for item in manifest["bindings"]:
    assert sha(Path(item["path"])) == item["sha256"], "Frozen read-only input changed"
numeric_bindings = gate["numeric_bindings"]
assert numeric_bindings
for rel, expected in numeric_bindings.items():
    p = (B / rel).resolve()
    assert p.is_relative_to(B) and rel.startswith("round20/")
    assert sha(p) == expected, "Frozen canonical numerical binding changed"
receipt_rel = gate["numeric_receipt_relative_path"]
assert receipt_rel in numeric_bindings
assert json.loads((B / receipt_rel).read_text(encoding="utf-8"))["exit_code"] == 0

fixed_bindings = {
    str(gate_path): sha(gate_path),
    str(PREP): sha(PREP),
    str(Path(__file__).resolve()): sha(Path(__file__)),
    str(manifest_path): sha(manifest_path),
    str(B / "round20" / "agent4_geometry_preparation.md"): prep["report_sha256"],
    str(W / "protocol_revision02.md"): prep["protocol_revision_sha256"],
    str(LEAN): prep["compiler_sha256"],
    str(PYTHON): prep["python_runtime_sha256"],
    str(W / "preparation.json"): prep["preserved_v1_preparation_sha256"],
    str(W / "preparation_v1_NOT_EXECUTED.json"): prep["preserved_v1_preparation_sha256"],
    str(W / "compile_once_v1_NOT_EXECUTED.py.txt"): prep["preserved_v1_launcher_sha256"],
    **{item["path"]: item["sha256"] for item in manifest["bindings"]},
    **{str(B / rel): expected for rel, expected in numeric_bindings.items()}}
for path, expected in fixed_bindings.items():
    assert sha(Path(path)) == expected, "Frozen launch linkage changed"

content = SRC.read_text(encoding="utf-8")
assert not re.search(r"\b(sorry|admit|native_decide|trustMe)\b", content)
assert not re.search(r"^\s*axiom\s+", content, re.M)
assert content.count("#print axioms") == prep["print_axioms_count"]
ledger_path = W / "geometry_build_receipt.json"
ledger = json.loads(ledger_path.read_text(encoding="utf-8")) if ledger_path.exists() else {
    "round": 20, "node": "14.5", "role": "source_geometry",
    "attempts": [], "successful_modules": {},
    "historical_source_compiles": 0, "victory": False, "score": 0}
assert not ledger["successful_modules"], "No replay of the unchanged geometry PASS"
if not ledger["attempts"]:
    assert sha(SRC) == prep["source_sha256"], "First attempt must use the exact reviewed source"
else:
    last = ledger["attempts"][-1]
    assert last["exit_code"] != 0, "Only an actual compiler failure authorizes repair"
    assert sha(SRC) != last["source_snapshot_sha256"], "Unchanged FAIL replay prohibited"
n = len(ledger["attempts"]) + 1
stem = f"attempt{n:02d}"
snapshot = W / (stem + "_source_PREEXEC.lean.txt")
launcher_snapshot = W / (stem + "_launcher_PREEXEC.py.txt")
with snapshot.open("xb") as h:
    h.write(SRC.read_bytes())
with launcher_snapshot.open("xb") as h:
    h.write(Path(__file__).read_bytes())
env = dict(os.environ)
env["PYTHONDONTWRITEBYTECODE"] = "1"
env["LEAN_PATH"] = ";".join(map(str, [W, B / "round20" / "role4",
    B / "round19" / "judge" / "build", B / "round18" / "judge" / "build",
    B / "round16" / "judge" / "build", B / "round13" / "role4" / "dependencies",
    *[CACHE / p / ".lake" / "build" / "lib" for p in PACKAGES]]))
out = W / (stem + ".olean")
cmd = [str(LEAN), "-o", str(out), str(SRC)]
entry = {
    "attempt": n, "phase": "PREEXEC", "started_utc": now(),
    "source": str(SRC), "source_sha256": sha(SRC),
    "source_snapshot": str(snapshot), "source_snapshot_sha256": sha(snapshot),
    "launcher_snapshot": str(launcher_snapshot), "launcher_snapshot_sha256": sha(launcher_snapshot),
    "command": cmd, "cwd": str(W), "LEAN_PATH": env["LEAN_PATH"],
    "gate": str(gate_path), "gate_sha256": sha(gate_path),
    "preparation_sha256": sha(PREP), "input_bindings": manifest["bindings"],
    "numeric_bindings": numeric_bindings, "fixed_bindings": fixed_bindings,
    "initial_reviewed_source_sha256": prep["source_sha256"],
    "compiler_sha256": sha(LEAN), "python_runtime_sha256": sha(PYTHON),
    "historical_source_compiles": 0, "victory": False}
started = W / (stem + "_started.json")
write_new(started, entry)
run = subprocess.run(cmd, cwd=W, env=env, capture_output=True,
                     text=True, encoding="utf-8", errors="replace")
stdout_path = W / (stem + ".stdout.txt")
stderr_path = W / (stem + ".stderr.txt")
log = W / (stem + ".log")
for p, s in [(stdout_path, run.stdout), (stderr_path, run.stderr),
             (log, run.stdout + run.stderr)]:
    with p.open("x", encoding="utf-8") as h:
        h.write(s)
entry.update({
    "phase": "FINISHED", "finished_utc": now(), "exit_code": run.returncode,
    "started_receipt": str(started), "started_receipt_sha256": sha(started),
    "stdout": str(stdout_path), "stdout_sha256": sha(stdout_path),
    "stderr": str(stderr_path), "stderr_sha256": sha(stderr_path),
    "log": str(log), "log_sha256": sha(log),
    "olean": str(out) if out.exists() else None,
    "olean_sha256": sha(out) if out.exists() else None})
# Preserve the actual compiler exit and logs before any integrity decision.
raw_finished = W / (stem + "_finished_raw.json")
write_new(raw_finished, entry)
post_checks = {}
post_failures = []


def check_post(label, path, expected):
    try:
        actual = sha(path)
    except OSError:
        actual = None
    okay = actual == expected
    post_checks[label] = {"path": str(path), "expected_sha256": expected,
                          "actual_sha256": actual, "unchanged": okay}
    if not okay:
        post_failures.append(label)


check_post("source", SRC, entry["source_snapshot_sha256"])
check_post("source_snapshot", snapshot, entry["source_snapshot_sha256"])
check_post("launcher_snapshot", launcher_snapshot, entry["launcher_snapshot_sha256"])
check_post("started_receipt", started, entry["started_receipt_sha256"])
check_post("stdout", stdout_path, entry["stdout_sha256"])
check_post("stderr", stderr_path, entry["stderr_sha256"])
check_post("log", log, entry["log_sha256"])
if entry["olean_sha256"] is not None:
    check_post("compiler_output", out, entry["olean_sha256"])
for path, expected in fixed_bindings.items():
    check_post("frozen:" + path, Path(path), expected)
entry["raw_finished_receipt"] = str(raw_finished)
entry["raw_finished_receipt_sha256"] = sha(raw_finished)
entry["post_integrity"] = {"all_unchanged": not post_failures,
                           "failed_bindings": post_failures, "checks": post_checks}
entry["credited_pass"] = (run.returncode == 0 and not post_failures
                          and "sorryAx" not in run.stdout + run.stderr
                          and out.is_file())
ledger["attempts"].append(entry)
if entry["credited_pass"]:
    final = SRC.with_suffix(".olean")
    with final.open("xb") as h:
        h.write(out.read_bytes())
    ledger["successful_modules"][SRC.name] = {
        "attempt": n, "source": str(SRC), "source_sha256": sha(SRC),
        "olean": str(final), "olean_sha256": sha(final)}
with ledger_path.open("w", encoding="utf-8") as h:
    h.write(json.dumps(ledger, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"attempt": n, "module": SRC.name, "exit_code": run.returncode,
                  "credited_pass": entry["credited_pass"],
                  "post_integrity_unchanged": not post_failures,
                  "log": str(log), "victory": False}, ensure_ascii=False))
print(run.stdout + run.stderr)
sys.exit(run.returncode if run.returncode != 0 else (0 if entry["credited_pass"] else 2))
