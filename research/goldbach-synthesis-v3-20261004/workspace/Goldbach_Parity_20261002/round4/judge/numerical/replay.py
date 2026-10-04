"""Round-4 independent replay, exporting only to the judge's numerical folder."""
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
    paths += list((BASE / "round3").rglob("*"))
    paths += [BASE / "build-judge.ps1", BASE / "judge_receipt.json"]
    paths += [ROUND / name for name in (
        "affine_checks.py", "affine.json", "inverse_checks.py", "inverse.json")]
    return {str(p): digest(p) for p in paths
            if p.is_file() and p.suffix in (".json", ".py", ".ps1")
            and "__pycache__" not in p.parts}

before = snapshot()
comparisons = []
for stem in ("affine", "inverse"):
    filename = stem + "_checks.py"
    shutil.copyfile(ROUND / filename, OUTPUT / filename)
    module = importlib.import_module(stem + "_checks")
    module.ROOT = OUTPUT
    with (OUTPUT / (stem + "_replay.log")).open("w", encoding="utf-8") as log:
        with contextlib.redirect_stdout(log):
            module.run()
    original = json.loads((ROUND / (stem + ".json")).read_text(encoding="utf-8"))
    replay = json.loads((OUTPUT / (stem + ".json")).read_text(encoding="utf-8"))
    assert original == replay, stem
    assert replay["status"] == "PASS"
    actual_N = replay.get("N", replay.get("large_N_induced_character", {}).get("N"))
    assert actual_N == 100000000
    comparisons.append(dict(
        file=stem + ".json", all_fields_equal=True,
        original_sha256=digest(ROUND / (stem + ".json")),
        replay_sha256=digest(OUTPUT / (stem + ".json")),
    ))
after = snapshot()
assert before == after, "An original or previous numerical artifact changed"
receipt = dict(
    status="PASS", N=100000000,
    outputs_isolated=True, original_artifacts_preserved=True,
    checks=comparisons, production_sha256_before=before,
    production_sha256_after=after, wrapper_sha256=digest(Path(__file__)),
    limitations="Exact finite replay; no quantitative D_N bound",
)
(OUTPUT / "replay_receipt.json").write_text(
    json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: receipt[k] for k in (
    "status", "N", "outputs_isolated", "original_artifacts_preserved", "checks")}, indent=2))
