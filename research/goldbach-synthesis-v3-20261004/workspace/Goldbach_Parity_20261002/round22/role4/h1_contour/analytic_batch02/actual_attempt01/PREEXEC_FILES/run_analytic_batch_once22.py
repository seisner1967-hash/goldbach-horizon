"""SOURCE ONLY: four children, two actual judged dependencies, STOP_FIRST_FAIL.

No numerical verdict is a premise of these Lean proofs or a compiler gate.
The launcher requires a fresh bounded ROOT authorization of exact bytes.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
BATCH = BASE / "round22/role4/h1_contour/analytic_batch02"
SOURCES = BATCH / "source-final"
MANIFEST = BATCH / "prepared_manifest22.json"
GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_role4_analytic_batch02_authorization1.json"
OUTPUT = BATCH / "actual_attempt01"
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PACKAGES = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGE_NAMES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
EXPECTED_MODULES = ("GammaBoxBounds22", "GammaContourComponent22", "MellinThermal22", "MellinThermalInversion22")
EXPECTED_DEPENDENCIES = {"GammaPrerequisites22", "GammaDerivative22"}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def write(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write("\n")


def now():
    return datetime.now(timezone.utc).isoformat()


def check_bindings(items):
    changed = [item["path"] for item in items if sha(item["path"]) != item["sha256"]]
    if changed:
        raise RuntimeError(f"Changed immutable inputs: {changed}")
    return len(items)


def archives():
    registry = read(BASE / "round22/previous_artifacts_sha256.json")
    if registry["file_count"] != 3089:
        raise RuntimeError("Unexpected protected archive count")
    changed = [name for name, expected in registry["sha256"].items() if sha(BASE / name) != expected]
    if changed:
        raise RuntimeError(f"Changed protected archives: {changed}")
    return {"checked": 3089, "changed": [], "scope": "metadata only"}


def audit(text, declarations):
    matches = re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.DOTALL)
    rows = [{"declaration": item.group(1), "axioms": [a.strip() for a in (item.group(2) or "").split(",") if a.strip()]}
            for item in matches]
    exact = [row["declaration"] for row in rows] == ["GoldbachContinuous22." + name for name in declarations]
    standard = all(set(row["axioms"]) <= STANDARD_AXIOMS for row in rows)
    return rows, exact and standard and "sorryAx" not in text


def main():
    manifest, gate = read(MANIFEST), read(GATE)
    if manifest["status"] != "PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED":
        raise RuntimeError("Exact preparation not closed")
    if gate.get("schema") != "ROUND22_ROLE4_ANALYTIC_BATCH02_AUTHORIZATION_1" or gate.get("authorized") is not True:
        raise RuntimeError("Matching bounded ROOT authorization absent")
    if gate.get("compiler_invocations_max") != 4 or gate.get("stop_first_failure") is not True or gate.get("no_retry") is not True:
        raise RuntimeError("Four-child STOP_FIRST_FAIL/no-retry authorization absent")
    if gate.get("prepared_manifest_sha256") != sha(MANIFEST):
        raise RuntimeError("Gate does not bind this preparation")
    if tuple(item["module"] for item in manifest["modules"]) != EXPECTED_MODULES:
        raise RuntimeError("Compiled module list changed")
    if {item["module"] for item in manifest["judged_dependencies"]} != EXPECTED_DEPENDENCIES:
        raise RuntimeError("Read-only dependency list changed")
    if Path(sys.executable).resolve() != PYTHON.resolve():
        raise RuntimeError("Wrong Python runtime")
    check_bindings(manifest["immutable_inputs"])
    if sha(LEAN) != manifest["lean_sha256"] or sha(PYTHON) != manifest["python_sha256"]:
        raise RuntimeError("Pinned runtime changed")
    for dep in manifest["judged_dependencies"]:
        fin = read(dep["independent_fin_path"])
        if fin.get("status") != "INDEPENDENT_LEAN_AUX_PASS" or fin.get("exit_code") != 0 or fin.get("exact_axiom_coverage_standard_only") is not True:
            raise RuntimeError("Dependency lacks actual independent PASS")
        if fin["source_sha256"] != sha(dep["staged_source_path"]) or fin["olean_sha256"] != sha(dep["staged_olean_path"]):
            raise RuntimeError("Judged dependency bytes do not match their FIN")
    before = archives()
    OUTPUT.mkdir(exist_ok=False)
    captures = OUTPUT / "PREEXEC_FILES"
    captures.mkdir(exist_ok=False)
    capture_rows = []
    capture_items = manifest["capture_inputs"] + [{"path": str(MANIFEST), "name": "prepared_manifest22.json"},
                                                {"path": str(GATE), "name": "root_authorization1.json"}]
    for item in capture_items:
        original, target = Path(item["path"]), captures / item["name"]
        shutil.copyfile(original, target)
        if sha(target) != sha(original):
            raise RuntimeError("PREEXEC copy failed byte comparison")
        capture_rows.append({"original": str(original), "captured": str(target), "sha256": sha(target)})
    for dep in manifest["judged_dependencies"]:
        target = OUTPUT / (dep["module"] + ".olean")
        shutil.copyfile(dep["staged_olean_path"], target)
        if sha(target) != dep["olean_sha256"]:
            raise RuntimeError("Read-only judged dependency copy changed")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(OUTPUT)] + [str(PACKAGES / name / ".lake/build/lib") for name in PACKAGE_NAMES])
    write(OUTPUT / "PREEXEC.json", {"schema": "ROUND22_ROLE4_ANALYTIC_BATCH02_PREEXEC", "time_utc": now(),
        "captures": capture_rows, "lean_path": env["LEAN_PATH"], "manifest_sha256": sha(MANIFEST), "gate_sha256": sha(GATE),
        "archive_before": before, "input_bindings_checked": len(manifest["immutable_inputs"]), "compiler_invocations_max": 4,
        "compiler_invocations_role4_previously": 5, "numeric_invocations": 0, "old_bank_replay": 0,
        "judged_dependencies_recompiled": False})
    write(OUTPUT / "START.json", {"schema": "ROUND22_ROLE4_ANALYTIC_BATCH02_ACTUAL_START", "start_utc": now(),
        "preexec_sha256": sha(OUTPUT / "PREEXEC.json"), "manifest_sha256": sha(MANIFEST), "gate_sha256": sha(GATE),
        "compiler_invocations_max": 4, "stop_first_failure": True, "replayed": False})
    rows, failed = [], False
    for item in manifest["modules"]:
        module, source = item["module"], Path(item["staged_source_path"])
        text = source.read_text(encoding="utf-8-sig")
        if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", text):
            raise RuntimeError("Forbidden proof token in source")
        declarations = re.findall(r"^(?:theorem|def)\s+(\w+)", text, re.MULTILINE)
        prints = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", text, re.MULTILINE)
        if declarations != item["declarations"] or prints != declarations:
            raise RuntimeError("Qualified declaration audit coverage changed")
        command = [str(LEAN), "-DmaxHeartbeats=1000000", "-o", str(OUTPUT / (module + ".olean")), str(source)]
        start = now()
        write(OUTPUT / (module + "_START.json"), {"start_utc": start, "module": module, "command": command,
            "cwd": str(SOURCES), "source_sha256": sha(source), "child_index": len(rows) + 1, "no_retry": True})
        try:
            result = subprocess.run(command, cwd=SOURCES, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300, check=False)
            out, err, code = result.stdout, result.stderr, result.returncode
        except subprocess.TimeoutExpired as failure:
            out, err, code = failure.stdout or b"", failure.stderr or b"", 124
        except OSError as failure:
            out, err, code = b"", str(failure).encode("utf-8"), 127
        finish = now()
        stdout, stderr = OUTPUT / (module + ".stdout.log"), OUTPUT / (module + ".stderr.log")
        stdout.write_bytes(out)
        stderr.write_bytes(err)
        axiom_rows, valid = audit(out.decode("utf-8", errors="replace"), declarations)
        olean = OUTPUT / (module + ".olean")
        valid = valid and code == 0 and olean.is_file() and b"error:" not in out and b"error:" not in err
        row = {"module": module, "start_utc": start, "finish_utc": finish, "exit_code": code,
            "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr), "source_sha256": sha(source),
            "olean_sha256": sha(olean) if olean.is_file() else None, "qualified_axiom_rows": axiom_rows,
            "exact_standard_axiom_coverage": valid,
            "status": "AUTHOR_ANALYTIC_AUX_PASS_PENDING_JUDGE" if valid else "AUTHOR_ANALYTIC_FAIL"}
        write(OUTPUT / (module + "_FIN.json"), row)
        rows.append(row)
        if not valid:
            failed = True
            break
    changed = [item["path"] for item in manifest["immutable_inputs"] if sha(item["path"]) != item["sha256"]]
    after = archives()
    write(OUTPUT / "POSTEXEC.json", {"time_utc": now(), "changed_inputs": changed,
        "archives": after, "bindings_checked": len(manifest["immutable_inputs"])})
    receipt = {"schema": "ROUND22_ROLE4_ANALYTIC_BATCH02_ACTUAL_RECEIPT", "finish_utc": now(),
        "status": "AUTHOR_ANALYTIC_BATCH_AUX_PASS_PENDING_JUDGE" if not failed and not changed else "AUTHOR_ANALYTIC_BATCH_FAIL",
        "rows": rows, "actual_child_invocations": len(rows), "max_child_invocations": 4,
        "modules_not_launched": [item["module"] for item in manifest["modules"][len(rows):]],
        "stop_first_failure": True, "retry_count": 0, "changed_inputs": changed,
        "preexec_sha256": sha(OUTPUT / "PREEXEC.json"), "start_sha256": sha(OUTPUT / "START.json"),
        "postexec_sha256": sha(OUTPUT / "POSTEXEC.json"), "captures": capture_rows,
        "judged_dependencies_recompiled": False, "mathematical_python_invocations": 0,
        "global_h1_certified": False, "D_N_paid": False, "win": False}
    write(OUTPUT / "receipt.json", receipt)
    print(json.dumps(receipt, ensure_ascii=False))
    return 1 if failed or changed else 0


if __name__ == "__main__":
    raise SystemExit(main())
