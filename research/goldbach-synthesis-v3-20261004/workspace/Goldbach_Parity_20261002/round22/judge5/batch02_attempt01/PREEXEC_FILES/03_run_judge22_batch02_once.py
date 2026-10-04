"""Independent three-module Lean audit. Closed until its exact ROOT gate exists."""
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
BASE = OWN.parents[1]
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
MODULES = ("EpsteinUnfold22", "EpsteinTail22", "GammaPrerequisites22")
DEPENDENCY_DIR = OWN / "batch01_attempt01"


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
    for row in inputs:
        actual = sha(row["path"])
        if verify and actual != row["sha256"]:
            raise RuntimeError("Frozen audit input changed: " + row["path"])
        rows.append({"path": row["path"], "sha256": actual})
    return rows


def archive_state(verify=True):
    path = BASE / "round22" / "previous_artifacts_sha256.json"
    binding = json.loads(path.read_text(encoding="utf-8"))
    rows = []
    for relative, expected in sorted(binding["sha256"].items()):
        actual = sha(BASE / relative)
        if verify and actual != expected:
            raise RuntimeError("Protected earlier archive changed: " + relative)
        rows.append({"path": relative, "sha256": actual})
    if len(rows) != binding["file_count"]:
        raise RuntimeError("Protected archive file count mismatch")
    return rows


def parse_axioms(log_text, expected):
    rows = []
    for name, values in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log_text, re.S):
        axioms = [word.strip() for word in values.replace("\n", " ").split(",") if word.strip()]
        rows.append({"declaration": name, "axioms": axioms})
    observed = [row["declaration"] for row in rows]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    valid = observed == expected and all(set(row["axioms"]) <= allowed for row in rows)
    forbidden_log = bool(re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", log_text))
    return rows, valid and not forbidden_log


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gate", required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if args.attempt != "batch02_attempt01":
        raise RuntimeError("Only one frozen batch02 attempt is allowed")
    gate_path = Path(args.gate).resolve()
    manifest_path = OWN / "batch02_prepared_manifest.json"
    catalog_path = OWN / "batch02_catalog.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    required = {"schema": "ROUND22_JUDGE5_BATCH02_AUTHORIZATION", "role": "ROLE5",
                "authorized": True, "attempt": args.attempt, "modules": list(MODULES),
                "compiler_invocations_maximum": 3, "source_manifest_sha256": sha(manifest_path),
                "launcher_sha256": sha(Path(__file__)), "python_sha256": PYTHON_SHA,
                "lean_sha256": LEAN_SHA, "numeric_banks": manifest["numeric_banks"], "numeric_banks_verified": True,
                "readonly_batch01_dependency_directory": str(DEPENDENCY_DIR),
                "independent_audit": True, "author_olean_allowed": False, "no_win": True}
    for key, value in required.items():
        if gate.get(key) != value:
            raise RuntimeError("ROOT audit gate mismatch: " + key)
    if (manifest["status"] != "PREPARED_SOURCE_ONLY_GATE_CLOSED"
            or manifest["modules"] != list(MODULES) or manifest["unresolved_modules"]
            or sha(catalog_path) != manifest["source_catalog_sha256"]):
        raise RuntimeError("Audit preparation is not closed")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN) != LEAN_SHA:
        raise RuntimeError("Runtime binding mismatch")
    for bank in manifest["numeric_banks"]:
        if sha(bank["path"]) != bank["sha256"]:
            raise RuntimeError("Genuine numeric bank binding changed")
    batch01_receipt = json.loads((DEPENDENCY_DIR / "receipt.json").read_text(encoding="utf-8"))
    if batch01_receipt["status"] != "INDEPENDENT_BATCH01_AUX_PASS":
        raise RuntimeError("Readonly judge dependencies are not independently certified")
    gate_sha = sha(gate_path)
    before = input_state(manifest["immutable_inputs"])
    archives_before = archive_state()
    out = OWN / args.attempt
    out.mkdir(exist_ok=False)
    captures = out / "PREEXEC_FILES"
    captures.mkdir()
    capture_paths = [OWN / "batch02_sources" / (module + ".lean") for module in MODULES]
    capture_paths += [Path(__file__), OWN / "prepare_judge22_batch02.py", OWN / "batch02_preparation.md",
                      OWN / "batch02_read_receipts.json", catalog_path, manifest_path,
                      OWN / "batch02_import_bindings.json", OWN / "batch02_batch01_bindings.json", gate_path]
    capture_paths += [Path(bank["path"]) for bank in manifest["numeric_banks"]]
    capture_paths += [Path(info["author_receipt"]) for info in catalog["modules"]]
    capture_paths += [Path(info["author_log"]) for info in catalog["modules"]]
    capture_paths += [OWN / "write_batch02_metadata_sources.py"]
    capture_paths += [BASE / "round22/role3/G0_final_catalog_v2.json", BASE / "round22/role3/G0_raccord_final.md"]
    copied = []
    for index, path in enumerate(capture_paths):
        target = captures / (str(index).zfill(2) + "_" + path.name)
        target.write_bytes(path.read_bytes())
        if sha(target) != sha(path):
            raise RuntimeError("PREEXEC capture mismatch")
        copied.append({"source": str(path), "capture": str(target), "sha256": sha(target)})
    paths = [out, DEPENDENCY_DIR] + [CACHE / package / ".lake" / "build" / "lib" for package in PACKAGES]
    if any(not path.is_dir() for path in paths):
        raise RuntimeError("Missing library directory")
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    commands = [[str(LEAN)] + info["compiler_options"] + ["-o", str(out / (module + ".olean")),
                 str(OWN / "batch02_sources" / (module + ".lean"))] for module, info in zip(MODULES, catalog["modules"])]
    write_new(out / "PREEXEC.json", {"time_utc": now(), "inputs": before, "captures": copied,
        "protected_archives": archives_before, "command_plan": commands,
        "cwd": str(OWN / "batch02_sources"), "LEAN_PATH": env["LEAN_PATH"],
        "python_sha256": sha(PYTHON), "lean_sha256": sha(LEAN),
        "mathlib_commit": "9837ca9d65d9de6fad1ef4381750ca688774e608",
        "gate_path": str(gate_path), "gate_sha256": gate_sha,
        "manifest_sha256": sha(manifest_path), "author_olean_in_lean_path": False})
    write_new(out / "START.json", {"time_utc": now(), "attempt": args.attempt,
        "scope": "INDEPENDENT_BATCH02_AUXILIARY_AUDIT_ONLY", "modules": list(MODULES),
        "gate_sha256": gate_sha, "child_invocations_maximum": 3, "hidden_retries": False})
    rows = []
    for module, command, info in zip(MODULES, commands, catalog["modules"]):
        if rows and rows[-1]["status"] != "INDEPENDENT_LEAN_AUX_PASS":
            break
        write_new(out / (module + "_START.json"), {"time_utc": now(), "module": module,
            "command": command, "scope": "INDEPENDENT_AUXILIARY_AUDIT_ONLY",
            "gate_sha256": gate_sha, "child_invocations_maximum": 1, "hidden_retries": False})
        started = now()
        timed_out = False
        try:
            completed = subprocess.run(command, cwd=str(OWN / "batch02_sources"), env=env,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       check=False, timeout=300)
            output, exit_code = completed.stdout, completed.returncode
        except subprocess.TimeoutExpired as error:
            output, exit_code, timed_out = error.stdout or b"", 124, True
        log_path = out / (module + ".log")
        log_path.write_bytes(output)
        axiom_rows, exact = parse_axioms(output.decode("utf-8", errors="replace"), info["qualified_prints"])
        olean = out / (module + ".olean")
        ok = exit_code == 0 and olean.is_file() and exact
        row = {"module": module, "started_at": started, "finished_at": now(),
               "command": command, "cwd": str(OWN / "batch02_sources"),
               "source_sha256": sha(info["source"]), "exit_code": exit_code, "timed_out": timed_out,
               "log_sha256": sha(log_path), "olean_sha256": sha(olean) if olean.is_file() else None,
               "axiom_rows": axiom_rows, "exact_axiom_coverage_standard_only": exact,
               "status": "INDEPENDENT_LEAN_AUX_PASS" if ok else "INDEPENDENT_LEAN_AUDIT_FAIL"}
        write_new(out / (module + "_FIN.json"), row)
        rows.append(row)
        print(json.dumps({key: value for key, value in row.items() if key != "axiom_rows"}, sort_keys=True), flush=True)
    post = input_state(manifest["immutable_inputs"], verify=False)
    archives_post = archive_state(verify=False)
    gate_unchanged = sha(gate_path) == gate_sha
    unchanged = before == post and archives_before == archives_post and gate_unchanged
    write_new(out / "POSTEXEC.json", {"time_utc": now(), "inputs": post, "protected_archives": archives_post,
        "all_inputs_unchanged": unchanged, "gate_sha256": sha(gate_path), "gate_unchanged": gate_unchanged})
    passed = unchanged and len(rows) == len(MODULES) and all(row["status"] == "INDEPENDENT_LEAN_AUX_PASS" for row in rows)
    write_new(out / "receipt.json", {"time_utc": now(), "attempt": args.attempt, "rows": rows,
        "actual_child_invocations": len(rows), "hidden_retries": False,
        "all_inputs_unchanged": unchanged, "author_olean_used": False,
        "status": "INDEPENDENT_BATCH02_AUX_PASS" if passed else "INDEPENDENT_BATCH02_FAILED",
        "module_count_passed": sum(row["status"] == "INDEPENDENT_LEAN_AUX_PASS" for row in rows),
        "declarations_passed": sum(len(row["axiom_rows"]) for row in rows if row["status"] == "INDEPENDENT_LEAN_AUX_PASS"),
        "batch01_recompiled": False, "readonly_local_dependencies": ["EpsteinKernel22", "EpsteinFinite22"],
        "global_trace_certified": False, "D_N_paid": False, "victory": False})
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
