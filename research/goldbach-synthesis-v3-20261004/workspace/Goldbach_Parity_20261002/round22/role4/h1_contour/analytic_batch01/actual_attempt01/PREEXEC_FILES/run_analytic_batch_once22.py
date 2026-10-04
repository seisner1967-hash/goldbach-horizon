"""SOURCE ONLY: five new analytic children, STOP_FIRST_FAIL, root gate required.

The judged Gamma dependency is copied without recompilation. No numeric
evaluation, installation, compiler probe, fallback, or retry exists here.
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
BATCH = BASE / "round22/role4/h1_contour/analytic_batch01"
MANIFEST = BATCH / "prepared_manifest22.json"
GATE = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_role4_analytic_batch01_authorization1.json"
OUTPUT = BATCH / "actual_attempt01"
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PACKAGES = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGE_NAMES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
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
    changed = [name for name, expected in registry["sha256"].items()
               if sha(BASE / name) != expected]
    if changed:
        raise RuntimeError(f"Changed protected archives: {changed}")
    return {"checked": 3089, "changed": [], "scope": "metadata only"}


def audit(text, declarations):
    rows = re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.DOTALL)
    parsed = [{"declaration": row.group(1),
               "axioms": [a.strip() for a in (row.group(2) or "").split(",") if a.strip()]}
              for row in rows]
    expected = ["GoldbachContinuous22." + name for name in declarations]
    exact = [row["declaration"] for row in parsed] == expected
    standard = all(set(row["axioms"]) <= STANDARD_AXIOMS for row in parsed)
    return parsed, exact and standard and "sorryAx" not in text


def main():
    manifest, gate = read(MANIFEST), read(GATE)
    if manifest["status"] != "PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED":
        raise RuntimeError("Preparation is not closed")
    if gate.get("schema") != "ROUND22_ROLE4_ANALYTIC_BATCH01_AUTHORIZATION_1":
        raise RuntimeError("Matching root authorization absent")
    if gate.get("authorized") is not True or gate.get("compiler_invocations_max") != 5:
        raise RuntimeError("Five-child bounded authorization absent")
    if gate.get("stop_first_failure") is not True or gate.get("no_retry") is not True:
        raise RuntimeError("STOP_FIRST_FAIL/no-retry authorization absent")
    if gate.get("prepared_manifest_sha256") != sha(MANIFEST):
        raise RuntimeError("Gate does not bind this preparation")
    if gate.get("existing_gamma_bank_provenance_verified") is not True:
        raise RuntimeError("Existing Gamma bank provenance not verified by root")
    if gate.get("source_bank_scope_compatibility_verified") is not True:
        raise RuntimeError("Root has not verified the auxiliary source/bank scope")
    if gate.get("auxiliary_compilation_despite_component_serialization_failure_authorized") is not True:
        raise RuntimeError("Root has not authorized the source proof after technical serialization failure")
    bank_path = Path(manifest["existing_gamma_bank_path"])
    if sha(bank_path) != gate["existing_gamma_bank_sha256"]:
        raise RuntimeError("Existing Gamma bank changed")
    bank = read(bank_path)
    if bank.get("status") != "GAMMA_ROTATED_LAPLACE_AUX_PASS":
        raise RuntimeError("Pinned Gamma bank is not its recorded auxiliary PASS")
    failure_path = Path(manifest["component_technical_failure_receipt_path"])
    if sha(failure_path) != gate["component_technical_failure_receipt_sha256"]:
        raise RuntimeError("Actual technical failure receipt changed")
    if gate.get("component_failure_technical_serialization_only_verified") is not True:
        raise RuntimeError("Root has not distinguished technical failure from a formula counterexample")
    if Path(sys.executable).resolve() != PYTHON.resolve():
        raise RuntimeError("Wrong Python runtime")
    check_bindings(manifest["immutable_inputs"])
    if sha(LEAN) != manifest["lean_sha256"] or sha(PYTHON) != manifest["python_sha256"]:
        raise RuntimeError("Pinned runtime changed")
    before = archives()
    OUTPUT.mkdir(exist_ok=False)
    captures = OUTPUT / "PREEXEC_FILES"
    captures.mkdir(exist_ok=False)
    capture_rows = []
    capture_items = manifest["capture_inputs"] + [
        {"path": str(MANIFEST), "name": "prepared_manifest22.json"},
        {"path": str(GATE), "name": "root_authorization1.json"},
        {"path": str(bank_path), "name": "existing_gamma_bank.json"},
        {"path": str(failure_path), "name": "component_technical_failure_receipt.json"}]
    for item in capture_items:
        original, target = Path(item["path"]), captures / item["name"]
        shutil.copyfile(original, target)
        if sha(target) != sha(original):
            raise RuntimeError("PREEXEC copy failed byte comparison")
        capture_rows.append({"original": str(original), "captured": str(target), "sha256": sha(target)})
    # Only actual judged dependency bytes are placed in the compiler search path.
    dependency = manifest["gamma_dependency"]
    shutil.copyfile(dependency["staged_olean_path"], OUTPUT / "GammaPrerequisites22.olean")
    if sha(OUTPUT / "GammaPrerequisites22.olean") != dependency["olean_sha256"]:
        raise RuntimeError("Judged Gamma dependency copy changed")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(OUTPUT)] +
        [str(PACKAGES / name / ".lake/build/lib") for name in PACKAGE_NAMES])
    write(OUTPUT / "PREEXEC.json", {"schema": "ROUND22_ROLE4_ANALYTIC_BATCH01_PREEXEC",
        "time_utc": now(), "captures": capture_rows, "lean_path": env["LEAN_PATH"],
        "manifest_sha256": sha(MANIFEST), "gate_sha256": sha(GATE),
        "existing_gamma_bank_sha256": sha(bank_path),
        "component_technical_failure_receipt_sha256": sha(failure_path), "archive_before": before,
        "input_bindings_checked": len(manifest["immutable_inputs"]),
        "compiler_invocations_max": 5, "compiler_invocations_role4_previously": 3,
        "numeric_invocations": 0, "old_bank_replay": 0, "gamma_dependency_recompiled": False})
    write(OUTPUT / "START.json", {"schema": "ROUND22_ROLE4_ANALYTIC_BATCH01_ACTUAL_START",
        "start_utc": now(), "preexec_sha256": sha(OUTPUT / "PREEXEC.json"),
        "manifest_sha256": sha(MANIFEST), "gate_sha256": sha(GATE),
        "compiler_invocations_max": 5, "stop_first_failure": True, "replayed": False})
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
        write(OUTPUT / (module + "_START.json"), {"start_utc": start, "module": module,
            "command": command, "cwd": str(BATCH / "sources"), "source_sha256": sha(source),
            "child_index": len(rows) + 1, "no_retry": True})
        try:
            result = subprocess.run(command, cwd=BATCH / "sources", env=env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300, check=False)
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
            "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr),
            "source_sha256": sha(source), "olean_sha256": sha(olean) if olean.is_file() else None,
            "qualified_axiom_rows": axiom_rows, "exact_standard_axiom_coverage": valid,
            "status": "AUTHOR_ANALYTIC_AUX_PASS_PENDING_JUDGE" if valid else "AUTHOR_ANALYTIC_FAIL"}
        write(OUTPUT / (module + "_FIN.json"), row)
        rows.append(row)
        if not valid:
            failed = True
            break
    post_changed = [item["path"] for item in manifest["immutable_inputs"]
                    if sha(item["path"]) != item["sha256"]]
    after = archives()
    write(OUTPUT / "POSTEXEC.json", {"time_utc": now(), "changed_inputs": post_changed,
        "archives": after, "bindings_checked": len(manifest["immutable_inputs"])})
    receipt = {"schema": "ROUND22_ROLE4_ANALYTIC_BATCH01_ACTUAL_RECEIPT", "finish_utc": now(),
        "status": "AUTHOR_ANALYTIC_BATCH_AUX_PASS_PENDING_JUDGE" if not failed and not post_changed else "AUTHOR_ANALYTIC_BATCH_FAIL",
        "rows": rows, "actual_child_invocations": len(rows), "max_child_invocations": 5,
        "modules_not_launched": [item["module"] for item in manifest["modules"][len(rows):]],
        "stop_first_failure": True, "retry_count": 0, "changed_inputs": post_changed,
        "preexec_sha256": sha(OUTPUT / "PREEXEC.json"), "start_sha256": sha(OUTPUT / "START.json"),
        "postexec_sha256": sha(OUTPUT / "POSTEXEC.json"), "captures": capture_rows,
        "gamma_dependency_recompiled": False, "mathematical_python_invocations": 0,
        "global_h1_certified": False, "D_N_paid": False, "win": False}
    write(OUTPUT / "receipt.json", receipt)
    print(json.dumps(receipt, ensure_ascii=False))
    return 1 if failed or post_changed else 0


if __name__ == "__main__":
    raise SystemExit(main())
