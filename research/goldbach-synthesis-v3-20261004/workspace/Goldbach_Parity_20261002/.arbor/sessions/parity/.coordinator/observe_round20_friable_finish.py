"""Metadata, hashes and stored labels only; no factor/log/sign recomputation."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
OWN = B / "round20/role6_friable"
OUT = OWN / "canonical_attempt01"

def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

receipt_path = OUT / "receipt.json"
receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
assert sha(receipt_path) == "545387c240e8d7c4d4f9c110b9ce3ef9dae0042e1452b7b51e5d1940b37045a1"
assert receipt["exit_code"] == 0 and receipt["launch_error"] is None
assert receipt["canonical_subprocess_count"] == 1 and receipt["routine_replays"] == 0
assert receipt["after_preservation_pass"] is True and receipt["frozen_input_changes_after"] == []
assert receipt["runtime_sha256_after"] == receipt["runtime_sha256"] == sha(receipt["runtime"])
assert sha(OUT / "started.json") == receipt["started_sha256"]
assert sha(receipt["log_path"]) == receipt["log_sha256"]
assert sha(receipt["result_path"]) == receipt["result_sha256"]
assert sha(receipt["input_manifest_path"]) == receipt["input_manifest_sha256"]
for record in receipt["captures_preexec"].values():
    assert sha(record["snapshot"]) == record["sha256"] == sha(record["original"])
result = json.loads(Path(receipt["result_path"]).read_text(encoding="utf-8"))
events = [json.loads(line) for line in Path(receipt["log_path"]).read_text(encoding="utf-8").splitlines() if line]
assert len(events) == 7 and events[-1]["stage"] == "FINAL_CANONICAL_NEW_FRIABLE20"
assert result["status"] == events[-1]["status"] == "PASS_NEW_FRIABLE20_FINITE_IDENTITIES_SOURCE_GUARDS_FALSE"
assert events[-1]["result_sha256"] == receipt["result_sha256"]
assert result["victory"] is False and result["source_budget_exponents_not_certified_by_finite_bank"] is True
assert result["float_operations"] == 0 and result["unresolved_signs"] == 0
assert result["old_producer_or_Lean_executions"] == 0
assert result["full_q_count"] == len(result["all_q_axes"]) == 1001
assert result["full_label_count"] == len(result["all_integer_e_q_labels_before_masks"]) == 54054
assert result["parameters_and_source_guards"]["Y_source_floor_certified"] == 1
assert result["parameters_and_source_guards"]["Y_test"] == 4096
assert result["parameters_and_source_guards"]["sigma_source"] is None
assert set(result["parameters_and_source_guards"]["source_guards"].values()) == {False}
for rec in result["full_Q_table_files"].values():
    assert sha(rec["path"]) == rec["sha256"]
assert sha(result["primitive_log_certificates"]["path"]) == result["primitive_log_certificates"]["sha256"]
stored_labels = Counter()
positions = []
def walk(value, path):
    if isinstance(value, dict):
        if {"lo", "hi", "width", "sign"} <= value.keys():
            label = value["sign"]
            assert label in {"POS", "NEG", "ZERO"}, (path, label)
            if label == "ZERO":
                assert value["lo"] == value["hi"] == value["width"] == "0/1", path
            stored_labels[label] += 1
            positions.append([path, label])
        for key, child in value.items():
            walk(child, path + "/" + key)
    elif isinstance(value, list):
        for i, child in enumerate(value):
            walk(child, path + "/" + str(i))
walk(result, "friable")
bindings = {}
for path in [Path(receipt["result_path"]), receipt_path, OUT / "started.json", OUT / "execution.log",
             OUT / "input_manifest.json", OWN / "preparation.json", OWN / "run_once.py"]:
    bindings[path.relative_to(B).as_posix()] = sha(path)
for rec in receipt["captures_preexec"].values():
    path = Path(rec["snapshot"])
    bindings[path.relative_to(B).as_posix()] = sha(path)
for rec in list(result["full_Q_table_files"].values()) + [result["primitive_log_certificates"]]:
    path = Path(rec["path"])
    bindings[path.relative_to(B).as_posix()] = sha(path)
obs = {
    "round": 20, "node": "14.5", "observed_at_utc": datetime.now(timezone.utc).isoformat(),
    "status": "ACTUAL_UNIQUE_NEW_FRIABLE_CANONICAL_PASS_OBSERVED_NO_SOURCE_PAYMENT",
    "full_receipt_root_read": "428da8", "full_log_root_read": "79f3f7",
    "actual_started_at_utc": receipt["started_at_utc"], "actual_finished_at_utc": receipt["finished_at_utc"],
    "actual_exit_code": 0, "receipt_sha256": sha(receipt_path),
    "log_sha256": receipt["log_sha256"], "result_sha256": receipt["result_sha256"],
    "capture_count": len(receipt["captures_preexec"]), "captures_and_current_originals_verified": True,
    "stored_shape": {"q": 1001, "e_labels": 54054, "counts": result["counts"],
                     "active_demands": len(result["all_active_friable_demand_weights"]),
                     "kernels": len(result["all_actual_new_kernels"]),
                     "unique_reciprocals": len(result["all_unique_F1_reciprocal_weights"]),
                     "unpaid_m1": len(result["F0_minus_F1_unpaid_m1"]),
                     "classes": len(result["affine_class_annex"]["all_class_rows"]),
                     "Euler_tuples": result["finite_Euler_Rankin_annex"]["tuple_count"],
                     "totient_axes": result["finite_totient_annex"]["integer_axes"],
                     "primitive_logs": result["primitive_log_certificates"]["primitive_count"]},
    "stored_certificate_positions": len(positions), "stored_certificate_labels": dict(stored_labels),
    "stored_position_label_encoding_sha256": hashlib.sha256(json.dumps(positions, separators=(",", ":")).encode()).hexdigest(),
    "labels_read_only_no_log_or_sign_recomputation": True,
    "new_numeric_bindings": bindings, "source_guards_false": True,
    "root_mathematical_execution": False, "root_lean_execution": False,
    "formal4_gate": "ELIGIBLE_AFTER_CURRENT_SOURCE_AND_BUILDER_REVIEW", "victory": False,
}
path = C / "messages/round20_friable_finish_root_observation.json"
with path.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(obs, f, ensure_ascii=False, indent=2)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = json.loads(cp_path.read_text(encoding="utf-8"))
cp["phase"] = "ROUND20_FRIABLE_CANONICAL_PASS_FORMAL4_SOURCE_REVIEW_COMPOSITE_GATE_CLOSED"
cp["last_progress"] += " Actual friable20 uniquePASS02:53:37..02:53:59UTC exit0,27captures preserved,1001q54054labels,H867F323,41active/56kernels/15recips/4unpaid,76800classes,2401Euler4096TK6938logs,0float/unresolved; allstored labels onlymetadata inspected, sourceguardsfalse/noWin. Formal4 eligible after source review, compiler still closed."
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"path": str(path), "sha256": sha(path), "numeric_bindings": len(bindings),
                  "stored_certificate_positions": len(positions), "stored_labels": dict(stored_labels),
                  "counts": obs["stored_shape"], "exit_code": 0, "victory": False}))
