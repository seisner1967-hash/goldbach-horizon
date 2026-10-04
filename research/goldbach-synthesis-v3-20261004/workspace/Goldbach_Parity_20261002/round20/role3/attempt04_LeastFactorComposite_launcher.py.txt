"""Compile one new ROLE3 module only after a concrete ROOT20 bank/compile gate.

This launcher is inert until invoked with a root-owned authorization file. It
never invokes a numeric producer, old compiler driver, Judge or version probe.
"""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
B = W.parents[1]
C = B / ".arbor/sessions/parity/.coordinator"
PREFIX = "GoldbachRound20.SwitchedComposite."
MODULES = ["OddBonferroniArithmetic", "LeastFactorComposite", "SwitchedSelbergWeight",
           "PhysicalCompositeSubtraction", "CompositeAPConductor", "SwitchedIncidenceEstimator"]
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
DECL = re.compile(r"^(def|theorem|lemma|structure)\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide|trustMe)\b")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def exclusive_json(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(value, ensure_ascii=False, indent=2) + "\n")

def relative(path):
    return path.relative_to(B).as_posix()

def bound_path(name):
    path = (B / name).resolve()
    if not path.is_relative_to(B) or not path.is_file():
        raise RuntimeError(f"invalid project-relative binding: {name}")
    return path

def verify_bindings(bindings, label):
    if not isinstance(bindings, dict) or not bindings:
        raise RuntimeError(f"missing {label} bindings")
    for name, digest in bindings.items():
        path = bound_path(name)
        if sha(path) != digest:
            raise RuntimeError(f"changed {label} binding: {name}")

def analyze_axioms(log, expected):
    pattern = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
    blocks = [(m.group(1), [a.strip() for a in (m.group(2) or "").split(",") if a.strip()])
              for m in pattern.finditer(log)]
    actual = [name for name, _ in blocks if name.startswith(PREFIX)]
    unexpected = {name: axioms for name, axioms in blocks
                  if name.startswith(PREFIX) and not set(axioms) <= ALLOWED_AXIOMS}
    return {"expected_declarations": expected, "actual_declarations": actual,
            "declaration_coverage_exact": actual == expected,
            "unexpected_axioms": unexpected,
            "axioms_by_declaration": {name: axioms for name, axioms in blocks if name.startswith(PREFIX)}}

def run(module, authorization, reason):
    preparation_path = W / "preparation.json"
    prep = json.loads(preparation_path.read_text(encoding="utf-8"))
    auth_path = authorization.resolve()
    if not auth_path.is_relative_to(C) or not auth_path.is_file():
        raise RuntimeError("authorization must be an existing root-owned coordinator file")
    auth = json.loads(auth_path.read_text(encoding="utf-8"))
    required = {
        "compile_authorization_token": "ROOT20_FORMAL3_COMPILE", "node_id": "13.12",
        "formal3_candidate_compilation_authorized": True,
        "root_full_read_current_formal3_sources_and_launcher_confirmed": True,
        "canonical_numeric_pass": True, "actual_identity_false": False,
        "actual_numeric_exit_code": 0
    }
    if any(auth.get(key) != value for key, value in required.items()):
        raise RuntimeError("ROOT20 authorization does not open the canonical bank/compile gate")
    if module not in auth.get("authorized_new_modules", []):
        raise RuntimeError("module not authorized")
    if auth.get("launcher_sha256") != sha(Path(__file__)):
        raise RuntimeError("launcher differs from the root-reviewed launcher")
    if auth.get("preparation_sha256") != sha(preparation_path):
        raise RuntimeError("preparation differs from the root-reviewed preparation")
    verify_bindings(auth.get("checked_inputs_sha256"), "canonical numeric bank")
    verify_bindings(prep.get("historical_dependencies_sha256"), "read-only historical import")
    lean = Path(prep["lean_executable"])
    if sha(lean) != LEAN_SHA or prep.get("lean_sha256") != LEAN_SHA:
        raise RuntimeError("Lean executable binding mismatch")
    if sha(Path(sys.executable)) != PYTHON_SHA or prep.get("python_sha256") != PYTHON_SHA:
        raise RuntimeError("Python executable binding mismatch")
    mathlib = Path(prep["mathlib_HEAD_path"]).parents[1]
    runtime_readonly = {
        Path(prep["mathlib_HEAD_path"]): prep["mathlib_HEAD_sha256"],
        mathlib / "Mathlib.lean": prep["mathlib_root_source_sha256"],
        mathlib / ".lake/build/lib/Mathlib.olean": prep["mathlib_root_olean_sha256"],
        lean: LEAN_SHA, Path(sys.executable): PYTHON_SHA
    }
    if any(not path.is_file() or sha(path) != digest for path, digest in runtime_readonly.items()):
        raise RuntimeError("runtime/cache binding mismatch")
    source = W / f"{module}.lean"
    text = source.read_text(encoding="utf-8-sig")
    code = text.split("-- AXIOM_AUDIT_BEGIN")[0]
    if FORBIDDEN.search(code):
        raise RuntimeError("forbidden proof token")
    declarations = [PREFIX + name for _, name in DECL.findall(code)]
    prints = re.findall(r"^#print axioms\s+(\S+)\s*$", text, re.M)
    if prints != declarations or len(set(declarations)) != len(declarations):
        raise RuntimeError("declaration audits are incomplete, duplicated or unordered")
    ledger_path = W / "build_receipt.json"
    ledger = json.loads(ledger_path.read_text(encoding="utf-8")) if ledger_path.exists() else {
        "node_id": "13.12", "role": 3, "round": 20, "victory": False, "attempts": []}
    previous = [a for a in ledger["attempts"] if a["module"] == module]
    source_sha = sha(source)
    if previous and previous[-1]["source_sha256"] == source_sha:
        raise RuntimeError("unchanged PASS or FAIL replay is prohibited")
    if any(a["status"] == "PASS_NEW_AUXILIARY_MODULE" for a in previous):
        raise RuntimeError("a previously passed module must not be rebuilt in this iteration")
    initial = auth.get("initial_sources_sha256")
    if not isinstance(initial, dict) or set(initial) != {relative(W / f"{m}.lean") for m in MODULES}:
        raise RuntimeError("root authorization must bind all six initial sources")
    if initial[relative(source)] != source_sha:
        if not previous or not auth.get("allow_source_changed_repairs_after_actual_failure") or not reason.strip():
            raise RuntimeError("source change requires an actual failed attempt and root-authorized repair")
    elif previous:
        raise RuntimeError("original source must not be replayed after an actual failed attempt")
    readonly = dict(prep["historical_dependencies_sha256"])
    for prior in MODULES[:MODULES.index(module)]:
        passes = [a for a in ledger["attempts"] if a["module"] == prior and a["status"] == "PASS_NEW_AUXILIARY_MODULE"]
        if not passes:
            raise RuntimeError(f"missing actual new PASS dependency: {prior}")
        receipt = passes[-1]
        readonly[receipt["source_path"]] = receipt["source_sha256"]
        readonly[receipt["olean_path"]] = receipt["olean_sha256"]
    verify_bindings(readonly, "historical and previously passed new dependency")
    build = W / "build"
    build.mkdir(exist_ok=True)
    output = build / f"{module}.olean"
    if output.exists():
        raise RuntimeError("unexpected pre-existing output; preserve and diagnose before execution")
    attempt = len(ledger["attempts"]) + 1
    stem = f"attempt{attempt:02d}_{module}"
    source_capture = W / f"{stem}_source.lean.txt"
    launcher_capture = W / f"{stem}_launcher.py.txt"
    auth_capture = W / f"{stem}_authorization.json.txt"
    for path, content in [(source_capture, source.read_bytes()),
                          (launcher_capture, Path(__file__).read_bytes()),
                          (auth_capture, auth_path.read_bytes())]:
        with path.open("xb") as stream:
            stream.write(content)
    env = dict(os.environ)
    dirs = [str(build)] + prep["historical_library_dirs"] + prep["cache_library_dirs"]
    if any(not Path(directory).is_dir() for directory in dirs):
        raise RuntimeError("missing declared Lean library directory")
    env["LEAN_PATH"] = os.pathsep.join(dirs)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    command = [str(lean), "-o", str(output), str(source)]
    start = {
        "node_id": "13.12", "role": 3, "attempt": attempt, "module": module,
        "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "actual_command": command, "cwd": str(W), "lean_path": dirs,
        "source_path": relative(source), "source_sha256": source_sha,
        "source_capture": relative(source_capture), "source_capture_sha256": sha(source_capture),
        "launcher_sha256": sha(Path(__file__)), "launcher_capture": relative(launcher_capture),
        "authorization_path": relative(auth_path), "authorization_sha256": sha(auth_path),
        "authorization_capture": relative(auth_capture), "preparation_sha256": sha(preparation_path),
        "checked_inputs_sha256": auth["checked_inputs_sha256"], "readonly_dependencies_sha256": readonly,
        "runtime_readonly_sha256": {str(path): digest for path, digest in runtime_readonly.items()},
        "expected_declarations": declarations, "repair_reason": reason,
        "old_rebuilds": 0, "old_PASS_replays": 0, "numeric_invocations": 0,
        "judge_invocations": 0, "victory": False
    }
    exclusive_json(W / f"{stem}_started.json", start)
    process = subprocess.run(command, cwd=W, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    log_bytes = process.stdout + process.stderr
    log_path = W / f"{stem}.log"
    with log_path.open("xb") as stream:
        stream.write(log_bytes)
    decoded = log_bytes.decode("utf-8", errors="replace")
    audit = analyze_axioms(decoded, declarations)
    source_unchanged = sha(source) == source_sha
    dependencies_unchanged = all(sha(bound_path(name)) == digest for name, digest in readonly.items())
    runtime_unchanged = all(path.is_file() and sha(path) == digest for path, digest in runtime_readonly.items())
    authorization_unchanged = sha(auth_path) == start["authorization_sha256"]
    bank_unchanged = all(sha(bound_path(name)) == digest for name, digest in auth["checked_inputs_sha256"].items())
    passed = (process.returncode == 0 and output.is_file() and source_unchanged and dependencies_unchanged
              and runtime_unchanged and authorization_unchanged and bank_unchanged
              and audit["declaration_coverage_exact"] and not audit["unexpected_axioms"])
    finish = dict(start)
    finish.update({
        "finished_utc": dt.datetime.now(dt.timezone.utc).isoformat(), "actual_exit_code": process.returncode,
        "status": "PASS_NEW_AUXILIARY_MODULE" if passed else "FAIL_ACTUAL_NEW_ATTEMPT",
        "log_path": relative(log_path), "log_sha256": sha(log_path), "axiom_audit": audit,
        "source_unchanged": source_unchanged, "readonly_dependencies_unchanged": dependencies_unchanged,
        "runtime_unchanged": runtime_unchanged, "authorization_unchanged": authorization_unchanged,
        "canonical_numeric_bank_unchanged": bank_unchanged,
        "written_definitions": sum(k == "def" for k, _ in DECL.findall(code)),
        "written_theorems": sum(k in ("theorem", "lemma") for k, _ in DECL.findall(code))
    })
    if output.is_file():
        captured = W / f"{stem}.olean"
        with captured.open("xb") as stream:
            stream.write(output.read_bytes())
        finish.update({"olean_path": relative(output), "olean_sha256": sha(output),
                       "olean_capture": relative(captured), "olean_capture_sha256": sha(captured)})
        if not passed:
            # Only this freshly generated file under this owned build directory.
            if not output.resolve().is_relative_to(build.resolve()):
                raise RuntimeError("output containment check failed")
            output.unlink()
            finish["failed_output_preserved_and_removed_from_import_path"] = True
    exclusive_json(W / f"{stem}_receipt.json", finish)
    ledger["attempts"].append(finish)
    ledger["actual_lean_invocations"] = len(ledger["attempts"])
    ledger["actual_passed_new_modules"] = sum(a["status"] == "PASS_NEW_AUXILIARY_MODULE" for a in ledger["attempts"])
    ledger_path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"attempt": attempt, "module": module, "status": finish["status"],
                      "actual_exit_code": process.returncode, "receipt": relative(W / f"{stem}_receipt.json"),
                      "axiom_coverage_exact": audit["declaration_coverage_exact"], "victory": False}, indent=2))
    print(decoded)
    return 0 if passed else (process.returncode or 97)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("module", choices=MODULES)
    parser.add_argument("--authorization", type=Path, required=True)
    parser.add_argument("--reason", default="Initial new candidate compilation after root canonical bank review")
    args = parser.parse_args()
    sys.exit(run(args.module, args.authorization, args.reason))
