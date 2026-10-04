"""Output-isolated exact round-7 replay; frozen source paths, no Lean calls."""
import contextlib
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode = True
OUTPUT = Path(__file__).resolve().parent
ROUND = OUTPUT.parents[1]
BASE = ROUND.parent
sys.path.insert(0, str(ROUND))
STATUS = {
    "logarithmic": "PASS_IDENTITY_ONLY",
    "jacobi": "PASS_IDENTITIES_ONLY",
    "trace": "PASS_EXACT_CONNECTION_ONLY",
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load_source(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    assert Path(module.__file__).resolve() == path.resolve()
    return module

manifest_path = ROUND / "previous_artifacts_sha256.json"
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
assert manifest["file_count"] == len(manifest["sha256"]) == 190
inputs_path = ROUND / "judge" / "input_sha256.json"
inputs = json.loads(inputs_path.read_text(encoding="utf-8"))
for relative, expected in inputs["sha256"].items():
    assert digest(ROUND / relative) == expected, relative

# Bind conservation explicitly: shared.py prepends old round directories.
# Old helper modules do not get to select the preservation registry.
preservation = load_source("conservation", ROUND / "conservation.py")
assert preservation.verify()["files"] == 190

def snapshot():
    paths = [BASE / relative for relative in manifest["sha256"]]
    paths += [ROUND / relative for relative in inputs["sha256"]]
    paths += [inputs_path, manifest_path, ROUND / "conservation.json"]
    return {str(p): digest(p) for p in paths}

before = snapshot()
comparisons = []
for stem, expected_status in STATUS.items():
    filename = stem + "_checks.py"
    source = ROUND / filename
    shutil.copyfile(source, OUTPUT / filename)
    module = load_source(stem + "_checks", source)
    assert module.verify.__globals__["BASELINE"] == manifest_path
    module.ROOT = OUTPUT
    with (OUTPUT / (stem + "_replay.log")).open("w", encoding="utf-8") as log:
        with contextlib.redirect_stdout(log):
            module.run()
    original = json.loads((ROUND / (stem + ".json")).read_text(encoding="utf-8"))
    replay = json.loads((OUTPUT / (stem + ".json")).read_text(encoding="utf-8"))
    assert original == replay, stem
    assert replay["status"] == expected_status and replay["N"] == 100000000
    assert replay["script_sha256"] == digest(source)
    assert digest(ROUND / (stem + ".json")) == digest(OUTPUT / (stem + ".json"))
    comparisons.append(dict(
        file=stem + ".json", status=replay["status"], all_fields_equal=True,
        original_sha256=digest(ROUND / (stem + ".json")),
        replay_sha256=digest(OUTPUT / (stem + ".json")),
        original_script_sha256=digest(source),
    ))
after = snapshot()
assert before == after, "An original or frozen artifact changed"
preserved = preservation.verify()
assert preserved["status"] == "PRESERVED" and preserved["files"] == 190
receipt = dict(
    status="PASS_EXACT_REPLAY", N=100000000, round=7,
    outputs_isolated=True, original_artifacts_preserved=True,
    preserved_previous_artifacts=preserved, checks=comparisons,
    production_sha256_before=before, production_sha256_after=after,
    wrapper_sha256=digest(Path(__file__)), input_manifest_sha256=digest(inputs_path),
    lean_invoked=False, new_lean_modules=0, new_lean_conclusions=0,
    limitations="Declared finite domains and exact diagnostics only; no signed/global D_N estimate",
)
(OUTPUT / "replay_receipt.json").write_text(
    json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: receipt[k] for k in (
    "status", "N", "outputs_isolated", "preserved_previous_artifacts", "checks", "lean_invoked")}, indent=2))
