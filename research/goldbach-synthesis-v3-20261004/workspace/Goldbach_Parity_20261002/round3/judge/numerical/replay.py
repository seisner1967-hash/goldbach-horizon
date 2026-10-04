"""Independent output-isolated replay of the unchanged round-3 Python sources."""
import contextlib
import hashlib
import importlib
import json
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode = True
OUTPUT = Path(__file__).resolve().parent
ROUND = OUTPUT.parents[1]
BASE = ROUND.parent
sys.path.insert(0, str(ROUND))

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot():
    paths = list((BASE / "numerical").rglob("*"))
    paths += [BASE / "build-judge.ps1", BASE / "judge_receipt.json"]
    paths += [ROUND / name for name in (
        "multifibre_checks.py", "multifibre.json",
        "mixed_difference_checks.py", "mixed_difference.json")]
    return {str(p): digest(p) for p in paths
            if p.is_file() and "__pycache__" not in p.parts}

before = snapshot()
for filename in ("multifibre_checks.py", "mixed_difference_checks.py"):
    shutil.copyfile(ROUND / filename, OUTPUT / filename)

# Only redirect the output directory; import, arithmetic, N and every selector
# still come from the original unchanged modules and their original BASE.
main = importlib.import_module("multifibre_checks")
main.ROOT = OUTPUT
with (OUTPUT / "multifibre_replay.log").open("w", encoding="utf-8") as log:
    with contextlib.redirect_stdout(log):
        main.run()
mixed = importlib.import_module("mixed_difference_checks")
with (OUTPUT / "mixed_difference_replay.log").open("w", encoding="utf-8") as log:
    with contextlib.redirect_stdout(log):
        mixed.run()

comparisons = []
for filename, omitted in (
    ("multifibre.json", {"elapsed_seconds", "previous_artifact_sha256"}),
    ("mixed_difference.json", {"main_receipt_sha256"}),
):
    original = json.loads((ROUND / filename).read_text(encoding="utf-8"))
    replay = json.loads((OUTPUT / filename).read_text(encoding="utf-8"))
    original_math = {k: v for k, v in original.items() if k not in omitted}
    replay_math = {k: v for k, v in replay.items() if k not in omitted}
    assert original_math == replay_math, filename
    assert replay["status"] == "PASS" and replay["N"] == 100000000
    comparisons.append(dict(
        file=filename, deterministic_fields_equal=True,
        excluded_metadata=sorted(omitted),
        original_sha256=digest(ROUND / filename),
        replay_sha256=digest(OUTPUT / filename),
    ))
after = snapshot()
assert before == after, "A production or previous numerical artifact changed"
receipt = dict(
    status="PASS", N=100000000,
    outputs_isolated=True, original_artifacts_preserved=True,
    checks=comparisons, production_sha256_before=before,
    production_sha256_after=after, wrapper_sha256=digest(Path(__file__)),
    limitations="Exact finite independent replay; no aggregate D_N estimate",
)
(OUTPUT / "replay_receipt.json").write_text(
    json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: receipt[k] for k in (
    "status", "N", "outputs_isolated", "original_artifacts_preserved", "checks")}, indent=2))
