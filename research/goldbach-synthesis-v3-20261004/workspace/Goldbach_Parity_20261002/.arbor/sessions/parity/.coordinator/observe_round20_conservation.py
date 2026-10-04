"""Read actual stored preflight20 evidence; never execute/replay its code."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
R = B / "round20"
def sha(p):
    h = hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda: f.read(1048576), b""):
            h.update(b)
    return h.hexdigest()
def read(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
startp = R / "role6/conservation_attempt01_started.json"
receiptp = R / "role6/conservation_attempt01_receipt.json"
sp, rp = read(startp), read(receiptp)
assert rp["exit_code"] == 0 and rp["subprocess_launch_error"] is None
assert rp["started_receipt_sha256"] == sha(startp)
assert rp["round"] == 20 and rp["attempt"] == 1
for k, v in sp.items():
    assert rp[k] == v, k
bindings = {}
for name, item in sp["captures_preexec"].items():
    original, snapshot = Path(item["original"]), Path(item["snapshot"])
    assert sha(original) == sha(snapshot) == item["sha256"], name
    assert original.stat().st_size == snapshot.stat().st_size == item["bytes"]
    bindings[name] = item
assert len(bindings) == 8
assert sha(Path(sp["python_executable"])) == sp["python_sha256"]
assert sha(Path(sp["root_authorization"])) == sp["root_authorization_sha256"]
resultp, logp = Path(rp["result"]), Path(rp["log"])
assert sha(resultp) == rp["result_sha256"]
assert sha(logp) == rp["log_sha256"]
result, log = read(resultp), read(logp)
assert result == log
registry = read(R / "previous_artifacts_sha256.json")
assert result["status"] == "PASS_EXACT_CONSERVATION"
assert result["expected_file_count"] == 1808
assert result["unchanged_between_stages"] is True
for stage in (result["before"], result["after"]):
    assert stage["passed"] is True
    assert stage["actual_file_count"] == stage["checked_sha256_count"] == 1808
    assert stage["exact_inventory_names"] == sorted(registry["sha256"])
    assert stage["observed_sha256"] == registry["sha256"]
    assert stage["original_hash_map_equal"] is True
    for key in ("missing", "extra", "changed", "original_mismatches"):
        assert stage[key] == [], key
assert result["mathematical_execution"] is False
assert result["protected_files_written"] == result["old_preflight_executions"] == 0
prospective = {}
for role, expected_note, expected_receipt, full_chunks in (
    (1, "1a4cbddf965c6584e0c35aa94a2407eeb1527b0f33dfa794532fbb75b4a88082", "8bb2475b5e46525f0f25a134779bc065f431bfd70a9ef22fe83b7189e5d7905a", ["2a4b5f", "011307"]),
    (2, "d26b6f010f57aa754d2b0429239ecc07ed9c1a629cacecac8d760360e33492ed", "08d7c73480bd2f653f4d33a014350842fb2397f404445c7a560542b919326468", ["241075", "606b75"]),
):
    note = C / f"messages/round20_role{role}_prospective.md"
    rec = C / f"messages/round20_role{role}_prospective_receipt.json"
    assert sha(note) == expected_note and sha(rec) == expected_receipt
    record = read(rec)
    items = record["input_bindings"] if role == 1 else record["inputs"]
    current = [{"path": i["path"], "recorded": i["sha256"], "actual": sha(Path(i["path"]))} for i in items]
    prospective[str(role)] = {"note_sha256": sha(note), "receipt_sha256": sha(rec), "root_full_read_chunks": full_chunks, "inputs_observed_current": current, "paper_only_not_selected": True}
observation = {
    "status": "ROOT_OBSERVED_ACTUAL_UNIQUE_PREFLIGHT20_PASS_NO_REPLAY",
    "observed_at_utc": datetime.now(timezone.utc).isoformat(),
    "started_at_utc": rp["started_at_utc"], "finished_at_utc": rp["finished_at_utc"],
    "exit_code": 0, "root_full_start_receipt_reads": ["d6f1f3", "84b27c"],
    "result_sha256": sha(resultp), "log_sha256": sha(logp), "receipt_sha256": sha(receiptp),
    "captures_preexec_verified": bindings, "stored_inventory_entries_verified": 1808,
    "whole_result_and_log_machine_read_equal": True,
    "historical_hashes_not_recomputed_by_root_in_this_observation": True,
    "prospective_paper_observations": prospective,
    "root_math_or_Lean_executions": 0, "victory": False,
}
out = C / "messages/round20_conservation_root_observation.json"
with out.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(observation, f, indent=2, sort_keys=True, ensure_ascii=False)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = read(cp_path)
cp.update(phase="ROUND20_PREFLIGHT_PASS_FINAL_IDEATIONS_PENDING", current_protected_artifacts=1808, current_protected_registry="round20/previous_artifacts_sha256.json", current_protected_registry_sha256=sha(R / "previous_artifacts_sha256.json"))
cp["previous_goal_turn_evidence"].extend([str(out.relative_to(B)).replace("\\", "/"), "round20/conservation.json", "round20/role6/conservation_attempt01_receipt.json"])
cp_path.write_text(json.dumps(cp, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"observation": str(out), "sha256": sha(out), "actual_exit_code": 0, "stored_bindings": 1808, "prospective_current_input_mismatches": {role: [i for i in data["inputs_observed_current"] if i["recorded"] != i["actual"]] for role, data in prospective.items()}}, indent=2))
