"""Authorize only reviewed new modules after actual fresh numerical PASS."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
W = B / "round20/role4"
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

obs_path = C / "messages/round20_friable_finish_root_observation.json"
assert sha(obs_path) == "21338c868e5d0de433f1838e1d72430c8def029c5e7dcf6d34d7ee41d4ccf821"
obs = json.loads(obs_path.read_text(encoding="utf-8"))
assert obs["actual_exit_code"] == 0 and obs["victory"] is False
bindings = obs["new_numeric_bindings"]
for relative, expected in bindings.items():
    assert relative.startswith("round20/") and sha(B / relative) == expected, relative
deps_path = W / "dependencies_readonly.json"
deps = json.loads(deps_path.read_text(encoding="utf-8"))["bindings"]
assert len(deps) == 18
for relative, expected in deps.items():
    assert sha(B / relative) == expected, relative
builder = W / "build.py"
assert sha(builder) == "89dea53493843f1196bdcdb2fd8ad376649870db665b1e8aef532e1bd6c8616a"
reviews = {
    "FriablePhysicalPrefix.lean": "9ff04a",
    "FriableEulerRankin.lean": "fb3f27",
    "FriableKernelEnvelope.lean": "f51bcd",
}
gate = {
    "authorization": "ROOT20_FORMAL4_COMPILE", "root_authorized": True,
    "canonical_new_numeric_pass_inspected": True, "round": 20, "node": "14.5",
    "authorized_at_utc": datetime.now(timezone.utc).isoformat(),
    "phase": 1, "scope": "ONLY_THREE_REVIEWED_NEW_MODULES",
    "authorized_new_modules": list(reviews),
    "initial_reviewed_source_sha256": {name: sha(W / name) for name in reviews},
    "full_root_source_read_chunks": reviews, "full_root_builder_read": "051395",
    "builder_sha256": sha(builder), "numeric_bindings": bindings,
    "numeric_receipt_relative_path": "round20/role6_friable/canonical_attempt01/receipt.json",
    "actual_numeric_exit_code": 0, "numeric_root_observation_sha256": sha(obs_path),
    "historical_dependencies_manifest_sha256": sha(deps_path),
    "historical_dependency_bindings_verified": 18,
    "current_preparation_metadata_sha256": sha(W / "preparation.json"),
    "root_lean_execution": False, "root_numeric_execution": False,
    "execution_policy": {
        "only_new_source_targets": True, "old_PASS_replay": False,
        "unchanged_PASS_replay": False, "historical_compilations": False,
        "source_correction_after_actual_failure_allowed": True,
        "every_actual_attempt_source_START_log_exit_preserved": True,
        "later_modules_need_separate_root_gate_after_FULL_read": True,
        "successful_sources_and_oleans_frozen": True,
        "definitional_or_local_PASS_is_not_victory": True,
    },
    "source_payment_established": False, "victory": False,
}
path = C / "messages/round20_formal4_authorization_phase1.json"
with path.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(gate, f, ensure_ascii=False, indent=2)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = json.loads(cp_path.read_text(encoding="utf-8"))
cp["phase"] = "ROUND20_FORMAL4_FIRST_THREE_NEW_MODULES_AUTHORIZED_COMPOSITE_GATE_CLOSED"
for item in cp["in_flight_executors"]:
    if item["role"] == 4:
        item["status"] = "PREFIX_EULER_KERNEL_NEW_COMPILATIONS_AUTHORIZED_OTHER_MODULES_GATE_CLOSED"
cp["last_progress"] += " Actual friable PASS observed25680a; first3Role4 reviewed FULL9ff04a/fb3f27/f51bcd +builder051395 and18readonlydeps/38numericbindings verified. Root gatephase1 onlyPrefix/Euler/Kernel permits truefailure corrections, noPASSreplay; other3 andROLE3 closed, noWin."
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"gate": str(path), "sha256": sha(path), "authorized_modules": list(reviews),
                  "verified_numeric_bindings": len(bindings), "verified_historical_bindings": 18,
                  "root_lean_executions": 0, "victory": False}))
