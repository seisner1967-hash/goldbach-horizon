"""One gated batch11 invocation of two projection auxiliaries in one source root."""
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
BASE = OWN.parent.parents[1]
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
MODULES = ("ThermalProjectionEnvelope22", "ThermalProjectionIdentity22")
LOCAL_DEPENDENCIES = ()


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
            raise RuntimeError("Frozen input changed: " + row["path"])
        rows.append({"path": row["path"], "sha256": actual})
    return rows


def archive_state(verify=True):
    binding = json.loads((BASE / "round22/previous_artifacts_sha256.json").read_text(encoding="utf-8"))
    rows = []
    for relative, expected in sorted(binding["sha256"].items()):
        actual = sha(BASE / relative)
        if verify and actual != expected:
            raise RuntimeError("Protected archive changed: " + relative)
        rows.append({"path": relative, "sha256": actual})
    if len(rows) != 3089 or binding["file_count"] != 3089:
        raise RuntimeError("Protected archive count mismatch")
    return rows


def parse_axioms(log_text, expected):
    pattern = r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
    rows = [{"declaration": name,
             "axioms": [word.strip() for word in (values or "").replace("\n", " ").split(",") if word.strip()]}
            for name, values in re.findall(pattern, log_text, re.S)]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    valid = ([row["declaration"] for row in rows] == expected
             and all(set(row["axioms"]) <= allowed for row in rows)
             and not re.search(r"\b(?:sorryAx|native_decide|Lean\.ofReduceBool)\b", log_text))
    return rows, bool(valid)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gate", required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if args.attempt != "batch11_attempt01":
        raise RuntimeError("Only the one frozen attempt is allowed")
    gate_path = Path(args.gate).resolve()
    manifest_path = OWN / "prepared_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    catalog = json.loads((OWN / "catalog.json").read_text(encoding="utf-8"))
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    required = {"schema": "ROUND22_JUDGE5_BATCH11_AUTHORIZATION", "role": "ROLE5", "authorized": True,
        "attempt": args.attempt, "modules": list(MODULES), "compiler_invocations_maximum": 2,
        "source_manifest_sha256": sha(manifest_path), "launcher_sha256": sha(Path(__file__)),
        "preparation_receipt_sha256": sha(OWN / "prepared_receipt.json"),
        "python_sha256": PYTHON_SHA, "lean_sha256": LEAN_SHA,
        "readonly_local_dependencies": list(LOCAL_DEPENDENCIES),
        "independent_audit": True, "author_olean_allowed": False, "no_win": True}
    for key, value in required.items():
        if gate.get(key) != value:
            raise RuntimeError("Separate ROOT gate mismatch: " + key)
    if (manifest["status"] != "PREPARED_SOURCE_ONLY_GATE_CLOSED" or manifest["unresolved_modules"]
            or manifest["modules"] != list(MODULES)
            or sha(OWN / "catalog.json") != manifest["source_catalog_sha256"]):
        raise RuntimeError("Preparation not closed")
    common_root = (OWN / "sources").resolve()
    if (Path(manifest["common_source_root"]).resolve() != common_root
            or Path(catalog["common_source_root"]).resolve() != common_root
            or any(Path(info["source"]).resolve().parent != common_root for info in catalog["modules"])):
        raise RuntimeError("Every source must be contained in the frozen common Lean root")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN) != LEAN_SHA:
        raise RuntimeError("Runtime binding mismatch")
    depdir = OWN / "readonly_oleans"
    if set(path.name for path in depdir.iterdir()) != {module + ".olean" for module in LOCAL_DEPENDENCIES}:
        raise RuntimeError("Unexpected local dependency")
    gate_sha = sha(gate_path)
    before = input_state(manifest["immutable_inputs"])
    archives_before = archive_state()
    out = OWN / args.attempt
    out.mkdir(exist_ok=False)
    capture_dir = out / "PREEXEC_FILES"
    capture_dir.mkdir()
    capture_paths = [Path(info["source"]) for info in catalog["modules"]]
    capture_paths += [OWN / name for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json",
        "read_receipts.json", "prepared_manifest.json", "prepared_receipt.json", "import_bindings.json", "closed_judge_bindings.json")]
    capture_paths += [gate_path, BASE / "round22/previous_artifacts_sha256.json"]
    capture_paths += [Path(info["original_source"]) for info in catalog["modules"]]
    capture_paths += [Path(path) for path in catalog["support_capture_paths"]]
    capture_paths += [Path(path) for path in catalog["author_provenance_capture_paths"]]
    for dep in catalog["dependency_bindings"]:
        capture_paths += [Path(dep[key]) for key in ("source", "olean_copy", "independent_receipt")]
        actual = Path(dep["independent_receipt"]).parent
        capture_paths.append(actual / (dep["module"] + "_FIN.json"))
    copied = []
    for index, path in enumerate(capture_paths):
        capture = capture_dir / (str(index).zfill(2) + "_" + path.name)
        capture.write_bytes(path.read_bytes())
        digest = sha(path)
        if sha(capture) != digest:
            raise RuntimeError("PREEXEC capture changed")
        copied.append({"source": str(path), "capture": str(capture), "sha256": digest})
    paths = [out, depdir] + [CACHE / package / ".lake/build/lib" for package in PACKAGES]
    if any(not path.is_dir() for path in paths):
        raise RuntimeError("Missing frozen library directory")
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    commands = [[str(LEAN)] + info["compiler_options"] + ["-o", str(out / (info["module"] + ".olean")), info["source"]]
                for info in catalog["modules"]]
    write_new(out / "PREEXEC.json", {"time_utc": now(), "inputs": before, "captures": copied,
        "protected_archives": archives_before, "command_plan": commands, "cwd": str(OWN / "sources"),
        "LEAN_PATH": env["LEAN_PATH"], "gate_path": str(gate_path), "gate_sha256": gate_sha,
        "manifest_sha256": sha(manifest_path), "python_sha256": sha(PYTHON), "lean_sha256": sha(LEAN),
        "mathlib_commit": "9837ca9d65d9de6fad1ef4381750ca688774e608",
        "author_olean_in_lean_path": False, "readonly_local_dependencies": list(LOCAL_DEPENDENCIES)})
    write_new(out / "START.json", {"time_utc": now(), "attempt": args.attempt,
        "scope": "INDEPENDENT_BATCH11_AUXILIARY_ONLY", "modules": list(MODULES),
        "gate_sha256": gate_sha, "child_invocations_maximum": 2, "hidden_retries": False})
    rows = []
    for info, command in zip(catalog["modules"], commands):
        if rows and rows[-1]["status"] != "INDEPENDENT_LEAN_AUX_PASS":
            break
        module = info["module"]
        write_new(out / (module + "_START.json"), {"time_utc": now(), "module": module,
            "command": command, "gate_sha256": gate_sha, "child_invocations_maximum": 1, "hidden_retries": False})
        started, timed_out, launch_error = now(), False, None
        try:
            completed = subprocess.run(command, cwd=str(OWN / "sources"), env=env,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False, timeout=300)
            output, code = completed.stdout, completed.returncode
        except subprocess.TimeoutExpired as error:
            output, code, timed_out = error.stdout or b"", 124, True
        except OSError as error:
            launch_error = str(error)
            output, code = launch_error.encode("utf-8"), 127
        log = out / (module + ".log")
        log.write_bytes(output)
        axioms, exact = parse_axioms(output.decode("utf-8", errors="replace"), info["qualified_prints"])
        obj = out / (module + ".olean")
        ok = code == 0 and obj.is_file() and exact
        row = {"module": module, "started_at": started, "finished_at": now(), "command": command,
            "source_sha256": sha(info["source"]), "source_prior_status": info["source_status"],
            "exit_code": code, "timed_out": timed_out, "launch_error": launch_error,
            "log_sha256": sha(log), "olean_sha256": sha(obj) if obj.is_file() else None,
            "axiom_rows": axioms, "exact_axiom_coverage_standard_only": exact,
            "status": "INDEPENDENT_LEAN_AUX_PASS" if ok else "INDEPENDENT_LEAN_AUDIT_FAIL"}
        write_new(out / (module + "_FIN.json"), row)
        rows.append(row)
        print(json.dumps({key: value for key, value in row.items() if key != "axiom_rows"}, sort_keys=True), flush=True)
    after = input_state(manifest["immutable_inputs"], verify=False)
    archives_after = archive_state(verify=False)
    unchanged_captures = all(sha(item["source"]) == item["sha256"] == sha(item["capture"]) for item in copied)
    unchanged_gate = sha(gate_path) == gate_sha
    unchanged = before == after and archives_before == archives_after and unchanged_captures and unchanged_gate
    write_new(out / "POSTEXEC.json", {"time_utc": now(), "inputs": after, "protected_archives": archives_after,
        "all_inputs_unchanged": unchanged, "captures_unchanged": unchanged_captures,
        "gate_unchanged": unchanged_gate, "gate_sha256": sha(gate_path)})
    passed = unchanged and len(rows) == len(MODULES) and all(row["status"] == "INDEPENDENT_LEAN_AUX_PASS" for row in rows)
    status = "INDEPENDENT_BATCH11_AUX_PASS" if passed else "INDEPENDENT_BATCH11_FAILED"
    write_new(out / "FIN.json", {"time_utc": now(), "attempt": args.attempt, "status": status, "actual_child_invocations": len(rows)})
    write_new(out / "receipt.json", {"time_utc": now(), "attempt": args.attempt, "status": status, "rows": rows,
        "actual_child_invocations": len(rows), "hidden_retries": False, "all_inputs_unchanged": unchanged, "all_current_bytes_preserved": unchanged,
        "modules_passed": sum(row["status"] == "INDEPENDENT_LEAN_AUX_PASS" for row in rows),
        "declarations_passed": sum(len(row["axiom_rows"]) for row in rows if row["status"] == "INDEPENDENT_LEAN_AUX_PASS"),
        "input_count": len(before), "closed_judge_file_count": manifest["closed_judge_files"],
        "protected_archive_count": len(archives_before), "capture_count": len(copied),
        "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "author_olean_used": False,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False,
        "H1_paid": False, "C3_paid": False, "C5_paid": False, "C6_paid": False,
        "global_trace_certified": False, "D_N_paid": False, "victory": False})
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
