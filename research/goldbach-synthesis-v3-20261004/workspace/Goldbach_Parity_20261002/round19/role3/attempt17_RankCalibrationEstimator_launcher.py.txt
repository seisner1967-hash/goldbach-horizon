"""One fresh role3 Lean module per invocation, after the root's numeric gate.

This is not a Judge or a mathematical/numeric producer. Every actual attempt
captures its source and launcher before subprocess, and preserves the real log.
Historical sources/oleans are read-only; no historical Lean is invoked.
"""
from datetime import datetime, timezone
import argparse
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
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ["aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq"]
MODULES = [
    "RankCalibrationFace", "RankCalibrationPrice", "RankCalibrationArithmetic",
    "RankCalibrationUnitLoss", "RankCalibrationEuler", "RankCalibrationEstimator",
]
DEPS = B / "round18" / "judge" / "build"
PREFIX = "GoldbachRound19.RankCalibration."
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
OLD_DEPS_SHA = {
    "SeparatedTypeII.lean": "4513f3323bbf475b329daf423de805eb207d3fe88793f91016369bcb0d5228d7",
    "SeparatedTypeII.olean": "896daceeb6a093f808313556ee63a93761ecd5831bc6279b8b88ffe9212d1dd5",
    "SeparatedTypeIICount.lean": "55ac598030d5bd67202553a5a8ffffc6fcc2ba3aa796428808aecb9586d5d5d1",
    "SeparatedTypeIICount.olean": "5ee894fa6a17f05bca328f743783ede1c27b40bd2e465efb22364b106f45a2fc",
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json_exclusive(path, obj):
    with Path(path).open("x", encoding="utf-8", newline="\n") as out:
        out.write(json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


def safe_bound(relative):
    p = (B / relative).resolve()
    if not p.is_relative_to(B.resolve()) or not p.is_file():
        raise RuntimeError("Gate binding outside project or missing: " + relative)
    return p


parser = argparse.ArgumentParser()
parser.add_argument("module", choices=MODULES)
parser.add_argument("--authorization", required=True)
parser.add_argument("--reason", default="Initial fresh compilation after canonical numeric PASS")
args = parser.parse_args()
auth_path = Path(args.authorization).resolve()
if not auth_path.is_relative_to((B / ".arbor" / "sessions" / "parity" / ".coordinator").resolve()):
    raise RuntimeError("Authorization must be a root coordinator file")
auth = json.loads(auth_path.read_text(encoding="utf-8"))
assert auth["compile_authorization_token"] == "ROOT19_FORMAL3_COMPILE"
assert auth["formal3_candidate_compilation_authorized"] is True
assert auth["canonical_numeric_pass"] is True
assert auth["actual_identity_false"] is False
assert args.module in auth["authorized_new_modules"]
assert auth["actual_numeric_exit_code"] == 0
assert auth["checked_inputs_sha256"], "Numeric bindings must not be empty"
checked = {}
for relative, digest in auth["checked_inputs_sha256"].items():
    path = safe_bound(relative)
    assert sha(path) == digest, "Root gate input changed: " + relative
    checked[relative] = digest
assert sha(LEAN) == LEAN_SHA
for name, digest in OLD_DEPS_SHA.items():
    assert sha(DEPS / name) == digest, "Protected read-only dependency changed: " + name

source = W / (args.module + ".lean")
source_bytes = source.read_bytes()
code = source.read_text(encoding="utf-8").split("-- AXIOM_AUDIT_BEGIN")[0]
assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustMe)\b", code)
decls = re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma|structure)\s+([A-Za-z][A-Za-z0-9_']*)", code, re.M)
printed = re.findall(r"^#print axioms ([A-Za-z0-9_.']+)\s*$", source.read_text(encoding="utf-8"), re.M)
assert printed == [PREFIX + name for name in decls], "Every new declaration must have its own axiom print"

receipt_path = W / "build_receipt.json"
record = json.loads(receipt_path.read_text(encoding="utf-8")) if receipt_path.exists() else {
    "attempts": [], "old_Lean_rebuilds": 0, "old_producers_replayed": 0,
    "old_oleans_copied": 0, "victory": False,
}
for previous in record["attempts"]:
    if previous["module"] == args.module and previous["exit_code"] == 0 and previous["source_sha256"] == sha(source):
        raise RuntimeError("Unchanged PASS must not be rerun")
module_index = MODULES.index(args.module)
for dep in MODULES[:module_index]:
    rows = [p for p in record["attempts"] if p["module"] == dep and p["exit_code"] == 0]
    assert rows, "Required new predecessor has no PASS: " + dep
    assert sha(W / (dep + ".lean")) == rows[-1]["source_sha256"]
    assert sha(W / (dep + ".olean")) == rows[-1]["olean_sha256"]

n = len(record["attempts"]) + 1
stem = "attempt%02d_%s" % (n, args.module)
capture = W / (stem + "_source.lean.txt")
with capture.open("xb") as out:
    out.write(source_bytes)
launcher_capture = W / (stem + "_launcher.py.txt")
with launcher_capture.open("xb") as out:
    out.write(Path(__file__).read_bytes())
gate_capture = W / (stem + "_authorization.json.txt")
with gate_capture.open("xb") as out:
    out.write(auth_path.read_bytes())
inputs = {str(DEPS / name): sha(DEPS / name) for name in OLD_DEPS_SHA}
for dep in MODULES[:module_index]:
    inputs[str(W / (dep + ".lean"))] = sha(W / (dep + ".lean"))
    inputs[str(W / (dep + ".olean"))] = sha(W / (dep + ".olean"))
env = dict(os.environ)
env["LEAN_PATH"] = ";".join(map(str, [W, DEPS, *[CACHE / p / ".lake" / "build" / "lib" for p in PACKAGES]]))
env["PYTHONDONTWRITEBYTECODE"] = "1"
env["PYTHONUTF8"] = "1"
olean = W / (args.module + ".olean")
command = [str(LEAN), "-o", str(olean), str(source)]
started = {
    "attempt": n, "module": args.module, "reason": args.reason, "state": "STARTED",
    "started_at_utc": datetime.now(timezone.utc).isoformat(), "command": command,
    "cwd": str(W), "LEAN_PATH": env["LEAN_PATH"], "lean_exe_sha256": sha(LEAN),
    "source": str(source), "source_sha256": sha(source), "source_capture": str(capture),
    "source_capture_sha256": sha(capture), "launcher_capture": str(launcher_capture),
    "launcher_capture_sha256": sha(launcher_capture), "authorization_capture": str(gate_capture),
    "authorization_capture_sha256": sha(gate_capture), "authorization_path": str(auth_path),
    "authorization_sha256": sha(auth_path), "checked_numeric_inputs_sha256": checked,
    "readonly_imports_sha256": inputs, "new_declarations": decls,
    "old_Lean_rebuilds": 0, "old_producers_replayed": 0, "old_oleans_copied": 0,
}
write_json_exclusive(W / (stem + "_started.json"), started)
proc = subprocess.run(command, cwd=W, env=env, capture_output=True)
log = W / (stem + ".log")
with log.open("xb") as out:
    out.write(proc.stdout + proc.stderr)
assert source.read_bytes() == source_bytes, "Concurrent source change during Lean"
for path, digest in inputs.items():
    assert sha(path) == digest, "Read-only import changed during Lean"
row = dict(started, state="FINISHED", finished_at_utc=datetime.now(timezone.utc).isoformat(),
           exit_code=proc.returncode, log=str(log), log_sha256=sha(log))
if proc.returncode == 0:
    preserved = W / (stem + "_fresh_pass.olean")
    with preserved.open("xb") as out:
        out.write(olean.read_bytes())
    row.update(olean=str(olean), olean_sha256=sha(olean),
               preserved_olean=str(preserved), preserved_olean_sha256=sha(preserved))
write_json_exclusive(W / (stem + "_receipt.json"), row)
record["attempts"].append(row)
receipt_path.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"attempt": n, "module": args.module, "exit_code": proc.returncode,
                  "source_sha256": sha(source), "log_sha256": sha(log)}, ensure_ascii=False))
print(log.read_text(encoding="utf-8", errors="replace"))
sys.exit(proc.returncode)
