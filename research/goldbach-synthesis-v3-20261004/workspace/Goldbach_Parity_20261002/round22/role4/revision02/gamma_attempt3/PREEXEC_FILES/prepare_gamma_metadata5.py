"""Metadata-only repair preparation. No Lean subprocess or mathematical calculation."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
from datetime import datetime, timezone

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
OWN = BASE / "round22" / "role4"
REV = OWN / "revision02"
PREVIOUS = OWN / "revision01" / "gamma_attempt2"


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write_new(name, value):
    with (REV / name).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def headers(source):
    return [re.sub(r"\s+", " ", m.group(0)).strip()
            for m in re.finditer(r"^(?:theorem|def)\s+\w+\b.*?:=", source, re.MULTILINE | re.DOTALL)]


def main():
    stamp = datetime.now(timezone.utc).isoformat()
    oldpath = OWN / "revision01" / "gamma_prepared_manifest4.json"
    old = read_json(oldpath)
    if old["status"] != "PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED":
        raise RuntimeError("The frozen original preparation4 has an unexpected status")
    inputs = {}
    for item in old["immutable_inputs"]:
        path = Path(item["path"])
        actual = sha(path)
        if actual != item["sha256"]:
            raise RuntimeError(f"Changed immutable input from preparation4: {path}")
        inputs[str(path)] = actual
    original = (OWN / "GammaPrerequisites22.lean").read_text(encoding="utf-8")
    revised_path = REV / "GammaPrerequisites22.lean"
    revised = revised_path.read_text(encoding="utf-8")
    imports = lambda s: re.findall(r"^import\s+(\S+)$", s, re.MULTILINE)
    if imports(original) != imports(revised):
        raise RuntimeError("The source repair changed the transitive import basis")
    if headers(original) != headers(revised) or len(headers(revised)) != 23:
        raise RuntimeError("The source repair changed a declaration statement or hypothesis")
    declarations = re.findall(r"^(?:theorem|def)\s+(\w+)", revised, re.MULTILINE)
    prints = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", revised, re.MULTILINE)
    if declarations != prints or len(prints) != 23:
        raise RuntimeError("Revised qualified axiom print coverage is not exact")
    if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", revised):
        raise RuntimeError("Forbidden proof token in revised source")
    previous_receipt = PREVIOUS / "receipt.json"
    previous = read_json(previous_receipt)
    if previous["exit_code"] != 1 or previous["compiler_invocations"] != 1:
        raise RuntimeError("Previous actual attempt does not match FAIL2")
    if previous["status"] != "AUTHOR_GAMMA_H2_COMPILE_FAIL" or previous["olean_sha256"] is not None:
        raise RuntimeError("Previous actual compiler status changed")
    stdout = (PREVIOUS / "stdout.log").read_text(encoding="utf-8")
    if stdout.count("error:") != 1 or stdout.count("sorryAx") != 4 or stdout.count("depends on axioms:") != 23:
        raise RuntimeError("FAIL2 technical error or audit count changed")
    for key, filename in (("stdout_sha256", "stdout.log"), ("stderr_sha256", "stderr.log"),
                          ("exit_sha256", "exit.json"), ("start_sha256", "START.json"),
                          ("preexec_sha256", "preexec.json")):
        if sha(PREVIOUS / filename) != previous[key]:
            raise RuntimeError(f"Changed preceding actual output: {filename}")
    for capture in previous["captured_inputs"]:
        for name in ("original", "captured"):
            path = Path(capture[name])
            if sha(path) != capture["sha256"]:
                raise RuntimeError(f"Changed original/capture from actual FAIL2: {path}")
            inputs[str(path)] = capture["sha256"]
    for path in PREVIOUS.rglob("*"):
        if path.is_file():
            inputs[str(path)] = sha(path)
    reads = [
        (revised_path, "FULL revised Gamma source", "6a3b09"),
        (REV / "run_gamma_once22_v5.py", "FULL new launcher, not executed", "6a3b09"),
        (REV / "gamma_preparation5.md", "FULL new preparation", "407316"),
        (REV / "prepare_gamma_metadata5.py", "FULL helper then read-identifiers patch", "407316"),
        (OWN / "revision01/gamma_attempt2_failure.md", "FULL new failure diagnosis", "407316"),
        (PREVIOUS / "stdout.log", "FULL actual FAIL2 raw output", "f8a86e"),
        (PREVIOUS / "receipt.json", "FULL actual FAIL2 receipt", "82359c"),
        (oldpath, "METADATA projection; all6415 input SHA checked, not FULL text", "preparation5 actual"),
        (Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\Analysis\SpecialFunctions\Pow\Continuity.lean"),
         "TARGETED header and lines1–90: global continuousAt_cpow_const", "e4b8ee, cb72c1, 5fb6df"),
    ]
    if any(scope == "PENDING_FULL_READ" for _, scope, _ in reads):
        raise RuntimeError("Required new source reads are not complete")
    write_new("gamma_read_receipts5.json", {
        "schema": "ROUND22_ROLE4_GAMMA_READ_RECEIPTS_5", "time_utc": stamp,
        "local_reads": [{"path": str(p), "sha256": sha(p), "scope": scope, "output_chunk": chunk}
                        for p, scope, chunk in reads],
        "previous_read_receipts_path": str(OWN / "revision01" / "gamma_read_receipts4.json"),
        "previous_read_receipts_sha256": sha(OWN / "revision01" / "gamma_read_receipts4.json"),
        "compiler_invocations_this_helper": 0, "compiler_invocations_role4_previously": 2,
        "mathematical_numeric_invocations": 0,
    })
    for path in (revised_path, REV / "run_gamma_once22_v5.py", REV / "prepare_gamma_metadata5.py",
                 REV / "gamma_preparation5.md", REV / "gamma_read_receipts5.json", oldpath,
                 OWN / "revision01/gamma_attempt2_failure.md"):
        inputs[str(path)] = sha(path)
    registry = read_json(BASE / "round22" / "previous_artifacts_sha256.json")
    if registry["file_count"] != 3089:
        raise RuntimeError("Unexpected archive registry")
    changed_archives = [name for name, expected in registry["sha256"].items() if sha(BASE / name) != expected]
    if changed_archives:
        raise RuntimeError(f"Protected archives changed: {changed_archives}")
    manifest = dict(old)
    manifest.update({
        "schema": "ROUND22_ROLE4_GAMMA_PREPARED_MANIFEST_5", "time_utc": stamp,
        "source_path": str(revised_path), "source_sha256": sha(revised_path),
        "original_source_sha256": sha(OWN / "GammaPrerequisites22.lean"),
        "previous_preparation_sha256": sha(oldpath),
        "previous_actual_receipt_path": str(previous_receipt),
        "previous_actual_receipt_sha256": sha(previous_receipt),
        "previous_actual_exit": 1, "previous_actual_error_count": 1,
        "previous_generated_sorryAx_declarations": 4,
        "declaration_statements_and_imports_unchanged": True,
        "launcher_sha256": sha(REV / "run_gamma_once22_v5.py"),
        "immutable_inputs": [{"path": p, "sha256": h} for p, h in sorted(inputs.items())],
        "preexec_captures": True, "exclusive_actual_start": True, "olean_hash_if_present": True,
        "revision4_inputs_verified": len(old["immutable_inputs"]),
        "compiler_invocations_this_helper": 0, "compiler_invocations_role4_previously": 2,
        "new_compiler_invocations_authorized": 0, "mathematical_numeric_invocations": 0,
        "archives_verified": 3089, "weil_certified": False, "zero_count_certified": False,
        "D_N_paid": False, "win": False,
    })
    write_new("gamma_prepared_manifest5.json", manifest)
    print(json.dumps({"status": manifest["status"], "previous_inputs_checked": len(old["immutable_inputs"]),
        "immutable_inputs": len(inputs), "modules": manifest["import_module_count"],
        "manifest_sha256": sha(REV / "gamma_prepared_manifest5.json"),
        "launcher_sha256": manifest["launcher_sha256"], "source_sha256": manifest["source_sha256"],
        "previous_actual_receipt_sha256": manifest["previous_actual_receipt_sha256"],
        "declaration_statements_unchanged": True, "archives_verified": 3089,
        "compiler_invocations_this_helper": 0, "compiler_invocations_role4_previously": 2,
        "mathematical_numeric_invocations": 0}, ensure_ascii=False))


if __name__ == "__main__":
    main()
