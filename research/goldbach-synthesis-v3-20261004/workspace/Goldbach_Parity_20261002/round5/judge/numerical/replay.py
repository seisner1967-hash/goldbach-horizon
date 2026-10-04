"""Independent round-5 numeric replay; all 120 frozen previous artifacts preserved."""
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

manifest_path = ROUND / "previous_artifacts_sha256.json"
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
assert manifest["file_count"] == 120
preservation = importlib.import_module("conservation")
assert preservation.verify()["status"] == "PRESERVED"

def snapshot():
    paths = [BASE / relative for relative in manifest["sha256"]]
    paths += [ROUND / name for name in (
        "previous_artifacts_sha256.json", "conservation.py", "conservation.json",
        "hecke_checks.py", "hecke.json", "frequency_checks.py", "frequency.json")]
    return {str(p): digest(p) for p in paths}

before = snapshot()
comparisons = []
for stem in ("hecke", "frequency"):
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
    actual_N = replay.get("N", replay.get("phase_reduction", {}).get("N"))
    assert actual_N == 100000000
    comparisons.append(dict(
        file=stem + ".json", all_fields_equal=True,
        original_sha256=digest(ROUND / (stem + ".json")),
        replay_sha256=digest(OUTPUT / (stem + ".json")),
    ))
after = snapshot()
assert before == after, "An original or frozen artifact changed"
preserved = preservation.verify()
assert preserved["status"] == "PRESERVED" and preserved["files"] == 120
receipt = dict(
    status="PASS", N=100000000,
    outputs_isolated=True, original_artifacts_preserved=True,
    preserved_previous_artifacts=preserved,
    checks=comparisons, production_sha256_before=before,
    production_sha256_after=after, wrapper_sha256=digest(Path(__file__)),
    limitations="Exact finite replay; no quantitative D_N bound",
)
(OUTPUT / "replay_receipt.json").write_text(
    json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: receipt[k] for k in (
    "status", "N", "outputs_isolated", "preserved_previous_artifacts", "checks")}, indent=2))
