"""Pre-execution static scope repair and metadata only; no compiler/test."""
import datetime as dt
import json
from pathlib import Path
import sys
import prepare_metadata as prep

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
archive = W / "scope_correction20"
archive.mkdir(exist_ok=False)
started = {
    "operation": "static_section_closure_repair_and_metadata_only",
    "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
    "actual_command": [sys.executable, "-B", str(Path(__file__))],
    "updater_sha256": prep.sha(Path(__file__)),
    "previous_preparation_sha256": prep.sha(W / "preparation.json"),
    "lean_invocations": 0, "numeric_invocations": 0, "actual_Lean_failures": 0
}
with (archive / "started.json").open("x", encoding="utf-8") as stream:
    stream.write(json.dumps(started, indent=2) + "\n")
with (archive / "updater.py.txt").open("xb") as stream:
    stream.write(Path(__file__).read_bytes())
with (archive / "preparation_PREUPDATE.json").open("xb") as stream:
    stream.write((W / "preparation.json").read_bytes())
for module in prep.MODULES:
    source = W / f"{module}.lean"
    with (archive / f"{module}_PREUPDATE.lean.txt").open("xb") as stream:
        stream.write(source.read_bytes())
    text = source.read_text(encoding="utf-8")
    tail = "\nend GoldbachRound20.SwitchedComposite\n"
    if text.count(tail) != 1 or "\nend\nend GoldbachRound20.SwitchedComposite" in text:
        raise RuntimeError(f"unexpected scope before repair: {module}")
    source.write_text(text.replace(tail, "\nend\nend GoldbachRound20.SwitchedComposite\n"),
                      encoding="utf-8", newline="\n")
manifest = prep.metadata(False)
manifest["preexecution_static_scope_correction"] = {
    "reason": "Close anonymous noncomputable section before closing named namespace",
    "updater_sha256": prep.sha(Path(__file__)),
    "previous_preparation_sha256": started["previous_preparation_sha256"],
    "source_snapshots": {prep.relative(p): prep.sha(p) for p in archive.glob("*_PREUPDATE.lean.txt")},
    "actual_Lean_failures": 0
}
(W / "preparation.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
                                     encoding="utf-8")
receipt = {
    "status": "STATIC_SCOPE_REPAIR_AND_METADATA_COMPLETE",
    "finished_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
    "started_sha256": prep.sha(archive / "started.json"),
    "updater_capture_sha256": prep.sha(archive / "updater.py.txt"),
    "preparation_sha256": prep.sha(W / "preparation.json"),
    "sources_sha256": {m["path"]: m["sha256"] for m in manifest["written_modules"]},
    "lean_invocations": 0, "numeric_invocations": 0, "actual_Lean_failures": 0
}
with (archive / "receipt.json").open("x", encoding="utf-8") as stream:
    stream.write(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))
