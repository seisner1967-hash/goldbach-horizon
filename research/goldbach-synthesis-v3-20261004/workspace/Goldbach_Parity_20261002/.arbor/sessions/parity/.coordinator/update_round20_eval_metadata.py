"""Replace inherited19 evaluation metadata before any20 mathematical execution."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess
import sys
B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
H = Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py")
P = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
prompt = B / ".arbor/sessions/parity/experiments/13.12/executor_prompt.md"
data = prompt.read_bytes()
assert b"round19\\judge\\run_once.py" in data
snapshot = C / "messages/round20_prompt13_12_before_eval_metadata_update.md"
with snapshot.open("xb") as f:
    f.write(data)
selected = json.loads((C / "messages/round20_role1_selection.json").read_text(encoding="utf-8"))
ctx = selected["helper_metadata_calls"][-1]["command"][-1]
ctx += " EvaluationInfo round20 is a planned independentJudge20 metadata target only: run_once.py does not yet exist and will not be invoked before allFINAL/freeze/FULLsourceReview/concreteJudgegate. Never invoke inheritedJudge19 or treat generateddefaultquickcheck instructions as authorization. This workspace is isolated by ownedround20directories, noGitstateaction required."
calls = []
def invoke(cmd, *args):
    argv = [str(P), "-B", "-X", "utf8", str(H), cmd, "--cwd", str(B), "--run-name", "parity", *args]
    p = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8")
    calls.append({"command": argv, "exit_code": p.returncode, "stdout": p.stdout, "stderr": p.stderr})
    if p.returncode:
        print(p.stdout, p.stderr)
        raise SystemExit(p.returncode)
eval_cmd = f'"{P}" -B -X utf8 "{B / "round20/judge/run_once.py"}"'
invoke("meta", "--set", "eval_cmd=" + eval_cmd, "--set", "dataset_info=Round20 inprogress:1808protected/uniqueconservationPASS;13.12actualBonferroni/compositeAPnewbank24m..48m preparationonly;ROLE2friablepending;sourceu1e24;41modules692aux unchanged;newJudge20plannedNOTYETCREATED_OR_AUTHORIZED;nooldreplay/noWin")
invoke("prompt-executor", "--node-id", "13.12", "--workdir", str(B), "--additional-context", ctx)
new = prompt.read_bytes()
assert b"round20\\judge\\run_once.py" in new
record = {"status": "ROUND20_INHERITED_EVAL19_METADATA_CORRECTED_BEFORE_EXECUTION", "updated_at_utc": datetime.now(timezone.utc).isoformat(), "original_prompt_full_read_chunk": "af947c", "previous_prompt_snapshot": str(snapshot), "previous_prompt_sha256": hashlib.sha256(data).hexdigest(), "new_prompt_sha256": hashlib.sha256(new).hexdigest(), "helper_metadata_calls": calls, "new_eval_target_exists": (B / "round20/judge/run_once.py").exists(), "new_eval_target_is_planned_only": True, "old_eval_execution_count": 0, "math_or_Lean_execution_count": 0, "victory": False}
out = C / "messages/round20_eval_metadata_update.json"
with out.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(record, f, indent=2, sort_keys=True, ensure_ascii=False)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = json.loads(cp_path.read_text(encoding="utf-8-sig"))
cp["previous_goal_turn_evidence"].append(str(out.relative_to(B)).replace("\\", "/"))
cp["coordination_incident"] = "Inheritedround19eval metadata found in generated13.12prompt before anymath20; nativePREUPDATEsnapshot preserved, meta andprompt20 updated sequentially exit0. AgentsnotifiednooldBdev; plannedJudge20targetnotexecutionauthorization. No unresolvedblocker."
cp_path.write_text(json.dumps(cp, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"metadata_update_sha256": hashlib.sha256(out.read_bytes()).hexdigest(), "new_prompt_sha256": record["new_prompt_sha256"], "helper_exit_codes": [i["exit_code"] for i in calls], "old_execution_count": 0}, indent=2))
