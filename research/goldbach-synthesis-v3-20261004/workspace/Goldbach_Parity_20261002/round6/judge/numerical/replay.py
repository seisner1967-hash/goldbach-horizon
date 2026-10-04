"""Round-6 output-isolated numeric replay; no Lean invocation or new theorem."""
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
assert manifest["file_count"] == 160
preservation = importlib.import_module("conservation")
assert preservation.verify()["status"] == "PRESERVED"

def snapshot():
    paths = [BASE / relative for relative in manifest["sha256"]]
    paths += [ROUND / name for name in (
        "previous_artifacts_sha256.json", "conservation.py", "conservation.json",
        "exact_tools.py", "katai_checks.py", "katai.json",
        "squarefree_checks.py", "squarefree.json",
        "agent1_finite_dilation.md", "agent2_coupled_squarefree.md",
        "agent3_contract_audit.md", "agent4_contract_audit.md", "agent6.md")]
    return {str(p): digest(p) for p in paths}

before = snapshot()
comparisons = []
for stem in ("katai", "squarefree"):
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
    expected_status = "PASS_CORRECTED_CONTRACT" if stem == "squarefree" else "PASS"
    assert replay["status"] == expected_status and replay["N"] == 100000000
    assert replay["script_sha256"] == digest(ROUND / filename)
    comparisons.append(dict(
        file=stem + ".json", status=replay["status"], all_fields_equal=True,
        original_sha256=digest(ROUND / (stem + ".json")),
        replay_sha256=digest(OUTPUT / (stem + ".json")),
        original_script_sha256=digest(ROUND / filename),
    ))
after = snapshot()
assert before == after, "An original or frozen artifact changed"
preserved = preservation.verify()
assert preserved["status"] == "PRESERVED" and preserved["files"] == 160
receipt = dict(
    status="PASS", N=100000000, round=6,
    outputs_isolated=True, original_artifacts_preserved=True,
    preserved_previous_artifacts=preserved,
    checks=comparisons, production_sha256_before=before,
    production_sha256_after=after, wrapper_sha256=digest(Path(__file__)),
    lean_invoked=False, new_lean_modules=0, new_lean_conclusions=0,
    limitations="Finite falsifiers and corrected identities; no D_N estimate or new Lean certificate",
)
(OUTPUT / "replay_receipt.json").write_text(
    json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: receipt[k] for k in (
    "status", "N", "outputs_isolated", "preserved_previous_artifacts", "checks", "lean_invoked")}, indent=2))
