"""Metadata-only revision3. No Lean invocation, imports of numerical packages, or mathematics."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
from datetime import datetime, timezone

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
OWN = BASE / "round22" / "role4"


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_new(name, value):
    with (OWN / name).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def main():
    stamp = datetime.now(timezone.utc).isoformat()
    oldpath = OWN / "gamma_prepared_manifest2.json"
    old = json.loads(oldpath.read_text(encoding="utf-8-sig"))
    if old["status"] != "PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED":
        raise RuntimeError("Revision2 not prepared")
    inputs = {}
    for item in old["immutable_inputs"]:
        path = Path(item["path"])
        actual = sha(path)
        if actual != item["sha256"]:
            raise RuntimeError(f"Changed immutable input from preparation2: {path}")
        inputs[str(path)] = actual
    reads = [
        (OWN / "GammaPrerequisites22.lean", "FULL final source unchanged", "5db356, ROOT701280"),
        (OWN / "run_gamma_once22_v2.py", "FULL unchanged preserved", "4c55aa, ROOT597c12"),
        (OWN / "prepare_gamma_metadata2.py", "FULL unchanged preserved", "a33aec, ROOTf9b2b4"),
        (OWN / "gamma_preparation2.md", "FULL unchanged preserved", "a30387, ROOTd27bbe"),
        (OWN / "run_gamma_once22_v3.py", "FULL revision3", "684eaa"),
        (OWN / "gamma_preparation3.md", "FULL revision3", "05b534"),
        (OWN / "prepare_gamma_metadata3.py", "FULL revision3 plus receipt identifiers patch", "3349c3"),
        (oldpath, "METADATA projection and every immutable input SHA; not FULL textual read", "ROOT73bfc5, ROLE4 preparation3 actual"),
    ]
    write_new("gamma_read_receipts3.json", {
        "schema": "ROUND22_ROLE4_GAMMA_READ_RECEIPTS_3", "time_utc": stamp,
        "local_reads": [{"path": str(p), "sha256": sha(p), "scope": scope, "output_chunk": chunk}
                        for p, scope, chunk in reads],
        "previous_read_receipts_path": str(OWN / "gamma_read_receipts2.json"),
        "previous_read_receipts_sha256": sha(OWN / "gamma_read_receipts2.json"),
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0,
    })
    for name in ("run_gamma_once22_v3.py", "prepare_gamma_metadata3.py", "gamma_preparation3.md",
                 "gamma_read_receipts3.json", "gamma_prepared_manifest2.json"):
        path = OWN / name
        inputs[str(path)] = sha(path)
    manifest = dict(old)
    manifest.update({
        "schema": "ROUND22_ROLE4_GAMMA_PREPARED_MANIFEST_3", "time_utc": stamp,
        "previous_preparation_sha256": sha(oldpath),
        "launcher_sha256": sha(OWN / "run_gamma_once22_v3.py"),
        "immutable_inputs": [{"path": p, "sha256": h} for p, h in sorted(inputs.items())],
        "preexec_captures": True, "exclusive_actual_start": True, "olean_hash_if_present": True,
        "revision2_inputs_verified": len(old["immutable_inputs"]),
    })
    write_new("gamma_prepared_manifest3.json", manifest)
    print(json.dumps({"status": manifest["status"], "previous_inputs_checked": len(old["immutable_inputs"]),
        "immutable_inputs": len(inputs), "modules": manifest["import_module_count"],
        "manifest_sha256": sha(OWN / "gamma_prepared_manifest3.json"),
        "launcher_sha256": manifest["launcher_sha256"], "source_sha256": manifest["source_sha256"],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0}, ensure_ascii=False))


if __name__ == "__main__":
    main()
