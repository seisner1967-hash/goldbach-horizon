"""Root metadata only: bind actual author receipts and authorize reviewed new sources."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
W = B / "round20/role4"
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):
    return json.loads(Path(p).read_text(encoding="utf-8-sig"))
def exclusive(p, obj):
    with Path(p).open("x", encoding="utf-8", newline="\n") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
        f.write("\n")

old_gate_path = C / "messages/round20_formal4_authorization_phase1.json"
assert sha(old_gate_path) == "9c606483ede95023f8d5ee8728649df4672d40672f73d4cfb710af31d3877493"
old_gate = load(old_gate_path)
for relative, expected in old_gate["numeric_bindings"].items():
    assert relative.startswith("round20/") and sha(B / relative) == expected, relative
deps_path = W / "dependencies_readonly.json"
assert sha(deps_path) == old_gate["historical_dependencies_manifest_sha256"]
deps = load(deps_path)["bindings"]
for relative, expected in deps.items():
    assert sha(B / relative) == expected, relative
builder_sha = "89dea53493843f1196bdcdb2fd8ad376649870db665b1e8aef532e1bd6c8616a"
assert sha(W / "build.py") == builder_sha
ledger_path = W / "build_receipt.json"
ledger = load(ledger_path)
assert [a["attempt"] for a in ledger["attempts"]] == list(range(1, 8))
observed = []
for a in ledger["attempts"]:
    assert a["phase"] == "FINISHED"
    for path_field, digest_field in [
        ("snapshot", "snapshot_sha256"),
        ("builder_snapshot", "builder_snapshot_sha256"),
        ("started_receipt", "started_receipt_sha256"),
        ("log", "log_sha256"),
    ]:
        assert sha(a[path_field]) == a[digest_field], (a["attempt"], path_field)
    assert a["snapshot_sha256"] == a["source_sha256"]
    assert a["builder_snapshot_sha256"] == builder_sha
    assert a["compile_gate_sha256"] == sha(old_gate_path)
    assert a["numeric_bindings"] == old_gate["numeric_bindings"]
    assert a["dependency_bindings"] == deps
    assert a["compiler_sha256"] == "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
    started = load(a["started_receipt"])
    for key in ["attempt", "started_utc", "source", "source_sha256", "snapshot", "command", "cwd", "LEAN_PATH"]:
        assert started[key] == a[key], (a["attempt"], key)
    if a["olean"] is not None:
        assert a["exit_code"] == 0 and sha(a["olean"]) == a["olean_sha256"]
    observed.append({key: a[key] for key in [
        "attempt", "source", "source_sha256", "snapshot", "snapshot_sha256",
        "started_utc", "finished_utc", "exit_code", "started_receipt_sha256",
        "log", "log_sha256", "olean", "olean_sha256"
    ]})
assert [a["exit_code"] for a in ledger["attempts"]] == [1, 1, 0, 1, 0, 1, 0]
passed_bindings = {}
for module, entry in ledger["successful_modules"].items():
    assert sha(entry["source"]) == entry["source_sha256"], module
    assert sha(entry["olean"]) == entry["olean_sha256"], module
    passed_bindings[str(Path(entry["source"]).relative_to(B)).replace("\\", "/")] = entry["source_sha256"]
    passed_bindings[str(Path(entry["olean"]).relative_to(B)).replace("\\", "/")] = entry["olean_sha256"]

expected_sources = {
    "FriablePrimeHarmonic.lean": "afcda87bb299e254f5680e5f95297144c61a8218b92f34309f6f390ddfdea224",
    "FriableTotientEnvelope.lean": "4ed2263d8836eb05824df6a857801404d3f6ee7a1efd9b3cf57b087e837b01b0",
    "FriablePhysicalPayment.lean": "8b5884ad66ef853a072058c1058fe5ff96caf654a3337917b4378b82aeb26e1f",
}
for module, expected in expected_sources.items():
    assert sha(W / module) == expected, module
assert sha(B / "round20/ideation_failure_feedback01.md") == "562783b7999486ee57fcb66743c08cd52017c3694bca75a45c61198ec9be7d5f"
now = datetime.now(timezone.utc).isoformat()
observation = {
    "observed_at_utc": now, "kind": "STORED_RECEIPTS_AND_BYTES_ONLY_NO_ROOT_COMPILATION",
    "round": 20, "role": 4, "ledger_sha256": sha(ledger_path),
    "actual_author_attempts": observed, "actual_author_pass_modules": passed_bindings,
    "actual_author_failure_count": 4, "actual_author_pass_count": 3,
    "full_root_log_reads": {"01": "3757d2", "02": "b93ec0", "03": "4a8e01", "04_05_06_07": "da69b7"},
    "feedback01_sha256": sha(B / "round20/ideation_failure_feedback01.md"),
    "feedback01_full_root_read": "d03381", "numerical_bindings_verified": len(old_gate["numeric_bindings"]),
    "historical_bindings_verified": len(deps), "root_lean_executions": 0,
    "root_mathematical_executions": 0, "independent_judge20_status": "NOT_YET_DISPATCHED",
    "victory": False,
}
observation_path = C / "messages/round20_formal4_phase1_root_observation.json"
exclusive(observation_path, observation)
gate = dict(old_gate)
gate.update({
    "authorized_at_utc": now, "phase": 2,
    "scope": "ONLY_THREE_REVIEWED_REMAINING_NEW_MODULES_AFTER_PHASE1_PASS",
    "authorized_new_modules": list(expected_sources),
    "initial_reviewed_source_sha256": expected_sources,
    "full_root_source_read_chunks": {"FriablePrimeHarmonic.lean": "b4e09a", "FriableTotientEnvelope.lean": "ecda78", "FriablePhysicalPayment.lean": "344791"},
    "phase1_root_observation_sha256": sha(observation_path),
    "phase1_frozen_import_bindings": passed_bindings,
    "current_preparation_metadata_sha256": sha(W / "preparation.json"),
    "source_payment_established": False,
    "scope_limits": ["F2_aggregation_all_e_open", "source_floors_ceils_geometry_wrapper_open", "F4_source_budget_open", "F0_minus_F1_unpaid", "full_residue_bridge_open"],
})
gate_path = C / "messages/round20_formal4_authorization_phase2.json"
exclusive(gate_path, gate)
cp_path = C / "checkpoint.json"
cp = load(cp_path)
cp["phase"] = "ROUND20_FORMAL4_PHASE2_NEW_COMPILATIONS_AUTHORIZED_COMPOSITE_GATE_CLOSED"
for item in cp["in_flight_executors"]:
    if item["role"] == 4:
        item["status"] = "PHASE1_THREE_AUTHOR_PASSES_FROZEN_PHASE2_THREE_REVIEWED_NEW_SOURCES_AUTHORIZED"
cp["last_progress"] += " Root metadata observes seven author4 attempts, four technical FAIL and three local PASS; all START/source/log/olean bindings verified, independentJudge20 pending. FULLphase2 reads b4e09a/ecda78/344791; new gate onlyPrimeHarmonic/TotientEnvelope/Payment, no successful-source replay; F2/source/F4/full bridge remain open."
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"observation": str(observation_path), "observation_sha256": sha(observation_path),
                  "gate": str(gate_path), "gate_sha256": sha(gate_path), "actual_author_attempts": 7,
                  "author_passes": 3, "author_failures": 4, "root_lean_executions": 0, "victory": False}))
