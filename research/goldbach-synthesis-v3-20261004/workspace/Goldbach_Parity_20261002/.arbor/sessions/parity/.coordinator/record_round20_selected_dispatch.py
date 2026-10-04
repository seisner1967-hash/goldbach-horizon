"""Persist actual selected20 agent dispatch; coordinator metadata only."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
def read(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
for role, expected in ((1, "76ec5e44560ee8f6b72e57079f8a0209f99a377a5a70b2b8bc257a2ead0c63d9"), (2, "3930ab3778ebf3e00bf80616b64d7d9ef63f6e80c2f74d63c8c5fbe7efe2944f")):
    p = C / f"messages/round20_role{role}_selection.json"
    assert sha(p) == expected
roles = [
    {"role": 3, "agent": "/root/round20_formal3_prepare", "node": "13.12", "ownership": ["round20/role3/**", "round20/agent3_formalisation.md"], "actual_dispatch": "spawn_preparatory_then_send_selected13.12_after_e00804", "status": "NEW_LEAN_SOURCEWRITING_COMPILER_GATE_CLOSED"},
    {"role": 4, "agent": "/root/round20_formal4_friable", "node": "14.5", "ownership": ["round20/role4/**", "round20/agent4_formalisation.md"], "actual_dispatch": "fresh_spawn_after97a00e", "status": "INDEPENDENT_PAPER_REVIEW_NEW_SOURCEWRITING_COMPILER_GATE_CLOSED"},
    {"role": 6, "agent": "/root/round20_numeric_preflight", "nodes": ["13.12", "14.5"], "ownership": ["round20/role6_composite/**", "round20/role6_friable/**", "round20/composite.json", "round20/friable.json"], "actual_dispatch": "followup_selected13.12_then_send_selected14.5", "status": "BOTH_NEW_NUMERICAL_SOURCE_PREPARATION_EXECUTION_GATES_CLOSED"},
]
record = {"status": "ROUND20_ACTUAL_SELECTED_DISPATCH_SIX_LOGICAL_ROLES_IN_WAVES", "recorded_at_utc": datetime.now(timezone.utc).isoformat(), "ideation_roles": {"1": "FROZEN_FINAL1", "2": "FROZEN_FINAL2"}, "active_worker_roles": roles, "role5_independent_judge": "NOT_DISPATCHED_UNTIL_ALL_FINAL_FROZEN", "protected_artifacts": 1808, "new_mathematical_execution_authorized_yet": False, "new_Lean_execution_authorized_yet": False, "official_retained_modules": 41, "official_retained_auxiliary_theorems": 692, "whole_ledger_paid": False, "victory": False}
out = C / "messages/round20_selected_dispatch.json"
with out.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(record, f, indent=2, sort_keys=True, ensure_ascii=False)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = read(cp_path)
cp["in_flight_executors"] = roles
cp["phase"] = "ROUND20_NEW_NUMERIC_AND_FORMAL_SOURCEWRITING_GATES_CLOSED"
cp["last_progress"] += " Both actualdispatches persisted, threeworkerroles3/4/6 active plusroot, ideation1/2FINAL, independentJudge5later; allnewmath/Lean gatesclosed,41/692officialunchanged,noWin."
cp["previous_goal_turn_evidence"].append(str(out.relative_to(B)).replace("\\", "/"))
cp_path.write_text(json.dumps(cp, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"dispatch_receipt_sha256": sha(out), "active_roles": [3, 4, 6], "math_execution": False, "victory": False}, indent=2))
