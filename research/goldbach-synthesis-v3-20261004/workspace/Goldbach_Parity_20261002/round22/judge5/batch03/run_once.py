"""One independent Lean child, only after the exact separate ROOT gate."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
MODULE = "GammaDerivative22"
DEPENDENCY_DIR = JUDGE / "batch02_attempt01"


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def write_new(path, data):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(data, stream, ensure_ascii=False, indent=2, sort_keys=True)
        stream.write("\n")


def input_state(inputs, verify=True):
    rows = []
    for item in inputs:
        actual = sha(item["path"])
        if verify and actual != item["sha256"]:
            raise RuntimeError("Frozen input changed: " + item["path"])
        rows.append({"path": item["path"], "sha256": actual})
    return rows


def archive_state(verify=True):
    data = json.loads((BASE / "round22/previous_artifacts_sha256.json").read_text(encoding="utf-8"))
    rows = []
    for relative, expected in sorted(data["sha256"].items()):
        actual = sha(BASE / relative)
        if verify and actual != expected:
            raise RuntimeError("Protected archive changed: " + relative)
        rows.append({"path": relative, "sha256": actual})
    if len(rows) != data["file_count"] or len(rows) != 3089:
        raise RuntimeError("Protected archive count mismatch")
    return rows


def parse_axioms(log_text, expected):
    rows = []
    for name, values in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log_text, re.S):
        rows.append({"declaration": name, "axioms": [word.strip() for word in values.replace("\n", " ").split(",") if word.strip()]})
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    exact = [item["declaration"] for item in rows] == expected and len(rows) == 8
    standard = all(set(item["axioms"]) <= allowed for item in rows)
    forbidden = bool(re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", log_text))
    return rows, exact and standard and not forbidden


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gate", required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if args.attempt != "batch03_attempt01":
        raise RuntimeError("Exactly one frozen attempt is allowed")
    gate_path = Path(args.gate).resolve()
    manifest_path, catalog_path = OWN / "prepared_manifest.json", OWN / "catalog.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    required = {"schema": "ROUND22_JUDGE5_BATCH03_AUTHORIZATION", "role": "ROLE5", "authorized": True,
        "attempt": args.attempt, "modules": [MODULE], "compiler_invocations_maximum": 1,
        "source_manifest_sha256": sha(manifest_path), "launcher_sha256": sha(Path(__file__)),
        "preparation_receipt_sha256": sha(OWN / "prepared_receipt.json"),
        "python_sha256": PYTHON_SHA, "lean_sha256": LEAN_SHA,
        "readonly_batch02_dependency_directory": str(DEPENDENCY_DIR), "independent_audit": True,
        "author_olean_allowed": False, "no_win": True}
    for key, value in required.items():
        if gate.get(key) != value:
            raise RuntimeError("ROOT gate mismatch: " + key)
    if (manifest["status"] != "PREPARED_SOURCE_ONLY_GATE_CLOSED" or manifest["modules"] != [MODULE]
            or manifest["unresolved_modules"] or sha(catalog_path) != manifest["source_catalog_sha256"]
            or catalog["total_declarations"] != 8 or catalog["module_count"] != 1):
        raise RuntimeError("Preparation not closed for exactly eight auxiliary declarations")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN) != LEAN_SHA:
        raise RuntimeError("Pinned runtime mismatch")
    previous = json.loads((DEPENDENCY_DIR / "receipt.json").read_text(encoding="utf-8"))
    if previous["status"] != "INDEPENDENT_BATCH02_AUX_PASS":
        raise RuntimeError("Own readonly Gamma prerequisite lacks independent PASS")
    gate_sha = sha(gate_path)
    before = input_state(manifest["immutable_inputs"])
    archives_before = archive_state()
    out = OWN / args.attempt
    out.mkdir(exist_ok=False)
    captures = out / "PREEXEC_FILES"
    captures.mkdir()
    info = catalog["modules"][0]
    capture_paths = [OWN / name for name in ("sources/GammaDerivative22.lean", "prepare_metadata.py", "run_once.py",
        "preparation.md", "catalog.json", "prepared_manifest.json", "prepared_receipt.json", "read_receipts.json",
        "import_bindings.json", "closed_judge_bindings.json")]
    author_actual = Path(info["author_receipt"]).parent
    capture_paths += [gate_path, Path(info["author_receipt"]), Path(info["author_log"]),
        author_actual / (MODULE + ".stderr.log"), author_actual / (MODULE + "_START.json"),
        author_actual / (MODULE + "_FIN.json"),
        BASE / ".arbor/sessions/parity/.coordinator/messages/round22_analytic_author01_observation.json"]
    bank_dir = BASE / "round22/role6/thermal_h1/revision01"
    capture_paths += [Path(bank["path"]) for bank in manifest["numeric_banks"]]
    capture_paths += [bank_dir / name for name in ("closure_receipt_r01.json", "closure_report_r01.md", "contract_r01.json")]
    copied = []
    for index, path in enumerate(capture_paths):
        target = captures / (str(index).zfill(2) + "_" + path.name)
        with target.open("xb") as stream:
            stream.write(path.read_bytes())
        if sha(target) != sha(path):
            raise RuntimeError("PREEXEC capture mismatch")
        copied.append({"source": str(path), "capture": str(target), "sha256": sha(target)})
    paths = [out, DEPENDENCY_DIR] + [CACHE / package / ".lake/build/lib" for package in PACKAGES]
    if any(not path.is_dir() for path in paths):
        raise RuntimeError("Missing pinned library directory")
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    command = [str(LEAN)] + info["compiler_options"] + ["-o", str(out / (MODULE + ".olean")), info["source"]]
    cwd = str(OWN / "sources")
    write_new(out / "PREEXEC.json", {"time_utc": now(), "inputs": before, "captures": copied,
        "protected_archives": archives_before, "command_plan": [command], "cwd": cwd, "LEAN_PATH": env["LEAN_PATH"],
        "python_sha256": sha(PYTHON), "lean_sha256": sha(LEAN),
        "mathlib_commit": "9837ca9d65d9de6fad1ef4381750ca688774e608", "gate_path": str(gate_path),
        "gate_sha256": gate_sha, "manifest_sha256": sha(manifest_path), "author_olean_in_lean_path": False,
        "readonly_local_dependencies": ["GammaPrerequisites22"], "old_batches_recompiled": False,
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False})
    started = now()
    write_new(out / "START.json", {"time_utc": started, "attempt": args.attempt, "modules": [MODULE],
        "scope": "INDEPENDENT_BATCH03_AUXILIARY_AUDIT_ONLY", "gate_sha256": gate_sha,
        "child_invocations_maximum": 1, "hidden_retries": False})
    write_new(out / (MODULE + "_START.json"), {"time_utc": started, "module": MODULE, "command": command,
        "cwd": cwd, "gate_sha256": gate_sha, "child_invocations_maximum": 1, "hidden_retries": False})
    timed_out, launch_error = False, None
    try:
        completed = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   check=False, timeout=300)
        stdout, stderr, exit_code = completed.stdout, completed.stderr, completed.returncode
    except subprocess.TimeoutExpired as error:
        stdout, stderr, exit_code, timed_out = error.stdout or b"", error.stderr or b"", 124, True
    except OSError as error:
        stdout, stderr, exit_code, launch_error = b"", str(error).encode("utf-8"), 127, str(error)
    finished = now()
    stdout_path, stderr_path = out / (MODULE + ".stdout.log"), out / (MODULE + ".stderr.log")
    for path, data in ((stdout_path, stdout), (stderr_path, stderr)):
        with path.open("xb") as stream:
            stream.write(data)
    axiom_rows, exact = parse_axioms((stdout + b"\n" + stderr).decode("utf-8", errors="replace"), info["qualified_prints"])
    olean = out / (MODULE + ".olean")
    ok = exit_code == 0 and olean.is_file() and exact
    row = {"module": MODULE, "started_at": started, "finished_at": finished, "command": command,
        "cwd": cwd, "source_sha256": sha(info["source"]), "exit_code": exit_code, "timed_out": timed_out,
        "launch_error": launch_error, "stdout_sha256": sha(stdout_path), "stderr_sha256": sha(stderr_path),
        "olean_sha256": sha(olean) if olean.is_file() else None, "axiom_rows": axiom_rows,
        "exact_axiom_coverage_standard_only": exact, "status": "INDEPENDENT_LEAN_AUX_PASS" if ok else "INDEPENDENT_LEAN_AUDIT_FAIL"}
    write_new(out / (MODULE + "_FIN.json"), row)
    print(json.dumps({key: value for key, value in row.items() if key != "axiom_rows"}, sort_keys=True), flush=True)
    post = input_state(manifest["immutable_inputs"], verify=False)
    archives_post = archive_state(verify=False)
    gate_unchanged = sha(gate_path) == gate_sha
    captures_unchanged = all(sha(item["source"]) == item["sha256"] == sha(item["capture"]) for item in copied)
    unchanged = before == post and archives_before == archives_post and gate_unchanged and captures_unchanged
    write_new(out / "POSTEXEC.json", {"time_utc": now(), "inputs": post, "protected_archives": archives_post,
        "all_inputs_unchanged": unchanged, "gate_sha256": sha(gate_path), "gate_unchanged": gate_unchanged,
        "captures_unchanged": captures_unchanged, "old_batches_recompiled": False})
    passed = ok and unchanged
    write_new(out / "FIN.json", {"time_utc": now(), "attempt": args.attempt, "actual_child_invocations": 1,
        "exit_code": exit_code, "status": "INDEPENDENT_BATCH03_AUX_PASS" if passed else "INDEPENDENT_BATCH03_FAILED"})
    write_new(out / "receipt.json", {"time_utc": now(), "attempt": args.attempt, "rows": [row],
        "actual_child_invocations": 1, "hidden_retries": False, "all_inputs_unchanged": unchanged,
        "capture_count": len(copied), "input_count": len(before), "protected_archive_count": len(archives_before),
        "closed_judge_file_count": manifest["closed_judge_files"], "author_olean_used": False,
        "status": "INDEPENDENT_BATCH03_AUX_PASS" if passed else "INDEPENDENT_BATCH03_FAILED",
        "modules_passed": int(passed), "declarations_passed": 8 if passed else 0,
        "old_batches_recompiled": False, "readonly_local_dependencies": ["GammaPrerequisites22"],
        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "global_trace_certified": False, "H1_paid": False, "C3_paid": False, "C5_paid": False,
        "D_N_paid": False, "victory": False})
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
