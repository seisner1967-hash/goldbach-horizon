"""Authorize only the FULL-reviewed new Demand extension after six real author PASSes."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
B=Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C=B/".arbor/sessions/parity/.coordinator"
W=B/"round20/role4"
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding="utf-8-sig"))
obs_path=C/"messages/round20_formal4_phase2_root_observation.json"
assert sha(obs_path)=="c9f3a66dde7d8e693a22a3db92c85607d98b386f6dd2db4384c37a3549c85eab"
obs=load(obs_path)
assert obs["author_pass_count"]==6 and obs["all_actual_author_attempts"]==16
base_path=W/"build_receipt.json"
assert sha(base_path)==obs["ledger_sha256"]=="acfa7776f904f6718de85466f3ca33e4798af51aefb0cb0dd87f5568fe42a1ad"
for rel,expected in obs["frozen_new_import_bindings"].items(): assert sha(B/rel)==expected,rel
prep_path=W/"extension_preparation_v2.json"
assert sha(prep_path)=="b08ae94b742c411b2fe9e9512c5bdf91a0aebd6c2bf684acbdcc165569e5fd02"
prep=load(prep_path)
assert prep["new_extension_Lean_invocations"]==0 and prep["status"]=="PREPARED_NOT_COMPILED"
assert prep["base_build_receipt_sha256"]==sha(base_path)
assert prep["post_integrity_checks"] and prep["unchanged_failure_replay_prohibited"]
for p,expected in prep["base_frozen_import_bindings"].items(): assert sha(p)==expected,p
builder=W/"build_extension.py"
assert sha(builder)==prep["builder_sha256"]=="4bcaafaf97a8a9e2e107d7b333427fdd772f58b748416f777b820daf885bfefa"
assert sha(W/"build.py")==prep["original_builder_sha256"]
assert prep["initial_reviewed_source_sha256"]=={"FriablePhysicalDemand.lean":"cf22fbe2d47460b4adb2dec1c7697421eafe85837de4a650b6715956c4676cb1"}
assert sha(W/"FriablePhysicalDemand.lean")==prep["initial_reviewed_source_sha256"]["FriablePhysicalDemand.lean"]
assert not (W/"extension_build_receipt.json").exists()
phase2_path=C/"messages/round20_formal4_authorization_phase2.json"
assert sha(phase2_path)=="48ff0f573a2bfb3a7b3db22bf789c457c58fc993ad999b67d4c48fae739e5d3d"
prior=load(phase2_path)
for rel,expected in prior["numeric_bindings"].items(): assert sha(B/rel)==expected,rel
deps_path=W/"dependencies_readonly.json"
assert sha(deps_path)==prep["historical_dependencies_manifest_sha256"]
deps=load(deps_path)["bindings"]
for rel,expected in deps.items(): assert sha(B/rel)==expected,rel
gate={
 "authorization":"ROOT20_FORMAL4_EXTENSION_COMPILE","root_authorized":True,
 "canonical_new_numeric_pass_inspected":True,"round":20,"node":"14.5","phase":3,
 "authorized_at_utc":datetime.now(timezone.utc).isoformat(),
 "authorized_new_modules":["FriablePhysicalDemand.lean"],
 "scope":"ONLY_NEW_PHYSICAL_DEMAND_MODULE_NO_BASE_OR_OTHER_EXTENSION_TARGET",
 "builder_sha256":sha(builder),"preparation_sha256":sha(prep_path),
 "initial_reviewed_source_sha256":prep["initial_reviewed_source_sha256"],
 "base_build_receipt_sha256":sha(base_path),"base_frozen_import_bindings":prep["base_frozen_import_bindings"],
 "numeric_bindings":prior["numeric_bindings"],
 "numeric_receipt_relative_path":prior["numeric_receipt_relative_path"],
 "actual_numeric_exit_code":0,"historical_dependencies_manifest_sha256":sha(deps_path),
 "full_root_source_read":"59eefc","full_root_launcher_read":"1783ba","full_root_preparation_read":"666de2",
 "six_base_sources_and_actual_receipts_root_observation_sha256":sha(obs_path),
 "policy":{"changed_repairs_only_after_actual_failure":True,"unchanged_FAIL_replay":False,
           "PASS_replay":False,"historical_compilations":False,"post_integrity_required":True,
           "every_actual_START_source_log_exit_preserved":True,"new_other_modules_need_separate_FULL_gate":True},
 "root_lean_executions":0,"root_mathematical_executions":0,"source_payment_established":False,"victory":False
}
out=C/"messages/round20_formal4_authorization_phase3.json"
with out.open("x",encoding="utf-8",newline="\n") as f:
 json.dump(gate,f,ensure_ascii=False,indent=2)
 f.write("\n")
cp_path=C/"checkpoint.json"
cp=load(cp_path)
cp["phase"]="ROUND20_NEW_DEMAND_EXTENSION_AUTHORIZED_GEOMETRY_AND_COMPOSITE_GATES_CLOSED"
for item in cp["in_flight_executors"]:
 if item["role"]==4: item["status"]="SIX_FROZEN_BASE_AUTHOR_PASSES_NEW_DEMAND_EXTENSION_PHASE3_AUTHORIZED_ONLY"
cp["last_progress"]+=" FULL Demand59eefc, launcher1783ba, prep666de2; six16-attempt base12bindings/38numeric/18hist verified; phase3 gate only newDemand changed-failure repairs, postintegrity, noPASSreplay. Sourcegeometry and composite still preEXEC, allFINAL20/Judge20 pending, noWin."
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"gate":str(out),"sha256":sha(out),"new_authorized_modules":gate["authorized_new_modules"],
                  "numeric_bindings":len(prior["numeric_bindings"]),"frozen_base_imports":12,"root_lean_executions":0,"victory":False}))
