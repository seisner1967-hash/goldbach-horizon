"""Prepared single Gamma compilation. This file has never been executed."""
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
OWN = BASE / "round22" / "role4"
SOURCE = OWN / "GammaPrerequisites22.lean"
MANIFEST = OWN / "gamma_prepared_manifest3.json"
GATE = BASE / ".arbor" / "sessions" / "parity" / ".coordinator" / "messages" / "round22_gamma_role4_authorization1.json"
OUTPUT = OWN / "gamma_attempt1"
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
PACKAGES = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGE_NAMES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write_new(path: Path, value) -> None:
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def verify_archives():
    registry = read_json(BASE / "round22" / "previous_artifacts_sha256.json")
    if registry["file_count"] != 3089:
        raise RuntimeError("Unexpected protected archive registry")
    changed = [name for name, expected in registry["sha256"].items()
               if sha(BASE / name) != expected]
    if changed:
        raise RuntimeError(f"Protected archive changed: {changed}")
    return {"checked": 3089, "changed": [], "scope": "metadata byte conservation only"}


def main() -> int:
    manifest = read_json(MANIFEST)
    if manifest.get("status") != "PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED":
        raise RuntimeError("Preparation dependencies are not closed")
    gate = read_json(GATE)
    if gate.get("schema") != "ROUND22_ROLE4_GAMMA_H2_LEAN_AUTHORIZATION_1":
        raise RuntimeError("No matching root authorization schema")
    if gate.get("authorized") is not True or gate.get("compiler_invocations") != 1:
        raise RuntimeError("Root has not authorized this one compilation")
    if gate.get("prepared_manifest_sha256") != sha(MANIFEST):
        raise RuntimeError("Authorization does not bind the frozen preparation")
    for item in manifest["immutable_inputs"]:
        path = Path(item["path"])
        if sha(path) != item["sha256"]:
            raise RuntimeError(f"Changed frozen input: {path}")
    bank_path = Path(gate["informative_gamma_bank_path"])
    if sha(bank_path) != gate["informative_gamma_bank_sha256"]:
        raise RuntimeError("Gamma bank hash mismatch")
    bank = read_json(bank_path)
    if gate.get("informative_gamma_bank_verified") is not True:
        raise RuntimeError("Root has not verified the informative Gamma bank")
    if bank.get("status") != gate.get("informative_gamma_bank_status"):
        raise RuntimeError("Gamma bank status mismatch")
    if "GAMMA" not in str(bank.get("status")) or "PASS" not in str(bank.get("status")):
        raise RuntimeError("An Epstein or unrelated bank cannot authorize Gamma")
    if sha(LEAN) != LEAN_SHA or sha(PYTHON) != PYTHON_SHA:
        raise RuntimeError("Existing runtime binary changed")
    if Path(sys.executable).resolve() != PYTHON.resolve():
        raise RuntimeError("Wrong Python launcher runtime")
    source = SOURCE.read_text(encoding="utf-8")
    if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source):
        raise RuntimeError("Forbidden proof token in new Gamma source")
    declarations = re.findall(r"^(?:theorem|def)\s+(\w+)", source, re.MULTILINE)
    prints = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", source, re.MULTILINE)
    if declarations != prints:
        raise RuntimeError("Qualified axiom print coverage is not exact")
    archive_before = verify_archives()
    OUTPUT.mkdir(exist_ok=False)
    captures = OUTPUT / "PREEXEC_FILES"
    captures.mkdir(exist_ok=False)
    capture_inputs = [
        (SOURCE, "GammaPrerequisites22.lean"),
        (Path(__file__), "run_gamma_once22_v3.py"),
        (OWN / "gamma_preparation3.md", "gamma_preparation3.md"),
        (OWN / "prepare_gamma_metadata3.py", "prepare_gamma_metadata3.py"),
        (OWN / "gamma_read_receipts3.json", "gamma_read_receipts3.json"),
        (MANIFEST, "gamma_prepared_manifest3.json"),
        (GATE, "root_authorization.json"),
        (bank_path, "informative_gamma_bank.json"),
    ]
    capture_receipts = []
    for original, name in capture_inputs:
        captured = captures / name
        shutil.copyfile(original, captured)
        if sha(captured) != sha(original):
            raise RuntimeError(f"PREEXEC capture mismatch: {original}")
        capture_receipts.append({"original": str(original), "captured": str(captured),
                                 "sha256": sha(captured)})
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(PACKAGES / name / ".lake" / "build" / "lib") for name in PACKAGE_NAMES)
    command = [str(LEAN), "-DmaxHeartbeats=1000000", "-o", str(OUTPUT / "GammaPrerequisites22.olean"), str(SOURCE)]
    preexec = {
        "schema": "ROUND22_ROLE4_GAMMA_PREEXEC_3",
        "time_utc": now(), "command": command, "cwd": str(OWN),
        "lean_path": env["LEAN_PATH"], "source_sha256": sha(SOURCE),
        "launcher_sha256": sha(Path(__file__)), "manifest_sha256": sha(MANIFEST),
        "gate_sha256": sha(GATE), "gamma_bank_sha256": sha(bank_path),
        "lean_sha256": sha(LEAN), "python_sha256": sha(PYTHON),
        "declarations": declarations, "compiler_invocations": 1,
        "mathematical_numeric_invocations": 0, "old_archive_replay": 0,
        "archive_before": archive_before,
        "captured_inputs": capture_receipts,
    }
    write_new(OUTPUT / "preexec.json", preexec)
    start = now()
    write_new(OUTPUT / "START.json", {
        "schema": "ROUND22_ROLE4_GAMMA_ACTUAL_START_3",
        "start_utc": start, "compiler_invocations_max": 1,
        "command": command, "cwd": str(OWN),
        "preexec_sha256": sha(OUTPUT / "preexec.json"),
        "gate_sha256": sha(GATE), "gamma_bank_sha256": sha(bank_path),
        "replayed": False,
    })
    try:
        process = subprocess.run(command, cwd=OWN, env=env, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, timeout=300, check=False)
        out, err, code = process.stdout, process.stderr, process.returncode
    except subprocess.TimeoutExpired as failure:
        out, err, code = failure.stdout or b"", failure.stderr or b"", 124
    except OSError as failure:
        out, err, code = b"", str(failure).encode("utf-8"), 127
    finish = now()
    (OUTPUT / "stdout.log").write_bytes(out)
    (OUTPUT / "stderr.log").write_bytes(err)
    write_new(OUTPUT / "exit.json", {"exit_code": code, "start_utc": start, "finish_utc": finish})
    changed = [item["path"] for item in manifest["immutable_inputs"] if sha(Path(item["path"])) != item["sha256"]]
    receipt = {
        "schema": "ROUND22_ROLE4_GAMMA_ACTUAL_RECEIPT_3",
        "start_utc": start, "finish_utc": finish, "exit_code": code,
        "compiler_invocations": 1, "old_archive_replay": 0,
        "source_sha256": sha(SOURCE), "preexec_sha256": sha(OUTPUT / "preexec.json"),
        "start_sha256": sha(OUTPUT / "START.json"),
        "captured_inputs": capture_receipts,
        "olean_sha256": sha(OUTPUT / "GammaPrerequisites22.olean")
            if (OUTPUT / "GammaPrerequisites22.olean").is_file() else None,
        "stdout_sha256": sha(OUTPUT / "stdout.log"), "stderr_sha256": sha(OUTPUT / "stderr.log"),
        "exit_sha256": sha(OUTPUT / "exit.json"), "changed_immutable_inputs": changed,
        "status": "AUTHOR_GAMMA_H2_COMPILE_PASS_PENDING_INDEPENDENT_JUDGE" if code == 0 and not changed else "AUTHOR_GAMMA_H2_COMPILE_FAIL",
        "weil_certified": False, "zero_count_certified": False,
        "D_N_paid": False, "win": False,
    }
    try:
        receipt["archive_after"] = verify_archives()
    except RuntimeError as failure:
        receipt["archive_after_error"] = str(failure)
        receipt["status"] = "AUTHOR_GAMMA_H2_COMPILE_FAIL"
        code = 3
    write_new(OUTPUT / "receipt.json", receipt)
    print(json.dumps(receipt, ensure_ascii=False))
    return code if not changed else 3


if __name__ == "__main__":
    raise SystemExit(main())

