"""Observe preserved author4 attempts08..16 and current bytes; no proof execution."""
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
prior_path = C / "messages/round20_formal4_phase1_root_observation.json"
assert sha(prior_path) == "3eed1dd2fc31f32a0e63b284302c0c9275a8bf643d15cc20fb1088c15486d5ad"
prior = load(prior_path)
gate_path = C / "messages/round20_formal4_authorization_phase2.json"
assert sha(gate_path) == "48ff0f573a2bfb3a7b3db22bf789c457c58fc993ad999b67d4c48fae739e5d3d"
gate = load(gate_path)
for rel, expected in gate["numeric_bindings"].items():
    assert sha(B / rel) == expected, rel
deps_path = W / "dependencies_readonly.json"
assert sha(deps_path) == gate["historical_dependencies_manifest_sha256"]
deps = load(deps_path)["bindings"]
for rel, expected in deps.items():
    assert sha(B / rel) == expected, rel
assert sha(W / "build.py") == gate["builder_sha256"]
ledger_path = W / "build_receipt.json"
ledger = load(ledger_path)
assert [a["attempt"] for a in ledger["attempts"]] == list(range(1, 17))
assert [a["exit_code"] for a in ledger["attempts"]] == [1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0]
observed = []
for a in ledger["attempts"][7:]:
    assert a["phase"] == "FINISHED"
    for path_key, digest_key in [("snapshot","snapshot_sha256"),
                                  ("builder_snapshot","builder_snapshot_sha256"),
                                  ("started_receipt","started_receipt_sha256"),
                                  ("log","log_sha256")]:
        assert sha(a[path_key]) == a[digest_key], (a["attempt"],path_key)
    assert a["snapshot_sha256"] == a["source_sha256"]
    assert a["builder_snapshot_sha256"] == gate["builder_sha256"]
    assert a["compile_gate_sha256"] == sha(gate_path)
    assert a["numeric_bindings"] == gate["numeric_bindings"]
    assert a["dependency_bindings"] == deps
    started = load(a["started_receipt"])
    for key in ["attempt","started_utc","source","source_sha256","snapshot","command","cwd","LEAN_PATH"]:
        assert started[key] == a[key], (a["attempt"],key)
    for p, expected in a["new_import_bindings"].items():
        assert sha(p) == expected, (a["attempt"],p)
    assert sha(a["command"][0]) == a["compiler_sha256"]
    if a["olean"] is not None:
        assert a["exit_code"] == 0 and sha(a["olean"]) == a["olean_sha256"]
    observed.append({k:a[k] for k in ["attempt","source","source_sha256","snapshot","snapshot_sha256",
                                     "started_utc","finished_utc","exit_code","started_receipt_sha256",
                                     "log","log_sha256","olean","olean_sha256"]})
assert len(ledger["successful_modules"]) == 6
frozen = {}
for module, entry in ledger["successful_modules"].items():
    assert sha(entry["source"]) == entry["source_sha256"]
    assert sha(entry["olean"]) == entry["olean_sha256"]
    for pkey,dkey in [("source","source_sha256"),("olean","olean_sha256")]:
        frozen[Path(entry[pkey]).relative_to(B).as_posix()] = entry[dkey]
feedback = {
    "round20/ideation_failure_feedback01.md":"562783b7999486ee57fcb66743c08cd52017c3694bca75a45c61198ec9be7d5f",
    "round20/ideation_failure_feedback02.md":"6063a7f05091c3b2ae641d9a984aaa27194aa0b9dc765ca44aaf66e79a5f852b",
    "round20/ideation_failure_feedback03.md":"c478b588394a15d6d6728c82cca02b8488d51fa5775c6d1b949e819a9e093923",
}
for rel,expected in feedback.items():
    assert sha(B / rel) == expected, rel
obs = {
    "observed_at_utc":datetime.now(timezone.utc).isoformat(),"round":20,"role":4,
    "kind":"STORED_RECEIPTS_AND_CURRENT_BYTES_ONLY_NO_ROOT_PROOF_OR_COMPILER_EXECUTION",
    "phase1_observation_sha256":sha(prior_path),"ledger_sha256":sha(ledger_path),
    "new_actual_author_attempts08_16":observed,"all_actual_author_attempts":16,
    "author_pass_count":6,"author_fail_count":10,"frozen_new_import_bindings":frozen,
    "full_root_final_sources":{
        "FriablePhysicalPrefix.lean":"a06ddd","FriableEulerRankin.lean":"331997",
        "FriableKernelEnvelope.lean":"411e9f","FriablePrimeHarmonic.lean":"a45291",
        "FriableTotientEnvelope.lean":"902986","FriablePhysicalPayment.lean":"6ae721"},
    "full_root_new_logs":{"08":"4f410f","09":"d2f74b","10":"5978c2","11":"24da83",
                          "12":"3009a8","13":"7596ff","14":"fd2791","15_16":"59eefc"},
    "feedback_bindings_verified":feedback,"full_root_feedback_reads":{"01":"d03381","02":"99e2d2","03":"430305"},
    "numeric_bindings_verified":len(gate["numeric_bindings"]),"historical_bindings_verified":len(deps),
    "root_lean_executions":0,"root_mathematical_executions":0,
    "independent_judge20_status":"NOT_YET_DISPATCHED_ALL_FINALS_PENDING",
    "open":["F2_all_e_aggregation","source_geometry_floors_ceils","F4_source_budget","F0_minus_F1","entire_residue_bridge"],
    "victory":False,
}
out_path = C / "messages/round20_formal4_phase2_root_observation.json"
with out_path.open("x",encoding="utf-8",newline="\n") as f:
    json.dump(obs,f,ensure_ascii=False,indent=2)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = load(cp_path)
cp["phase"] = "ROUND20_SIX_FORMAL4_AUTHOR_PASSES_FROZEN_NEW_EXTENSIONS_SOURCE_PREPARATION"
for item in cp["in_flight_executors"]:
    if item["role"] == 4:
        item["status"] = "SIX_AUTHOR_PASS_MODULES_FROZEN_DEMAND_AGGREGATION_GEOMETRY_PREPARATION_GATES_CLOSED"
cp["last_progress"] += " Six author4 modules PASS in16 actual compilations/10 preserved technicalFAIL; source/START/log/olean/currentimports and38numeric/18historical bytes verified. Allsix finalsources FULL read; feedback01/02/03 immutable. Demand/aggregation and parallelgeometry sourcewriting, 0extensionLean; composite gateclosed, allFINAL20/Judge20 pending, noWin."
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"observation":str(out_path),"sha256":sha(out_path),"author_attempts":16,
                  "author_passes":6,"author_failures":10,"frozen_bindings":len(frozen),"victory":False}))
