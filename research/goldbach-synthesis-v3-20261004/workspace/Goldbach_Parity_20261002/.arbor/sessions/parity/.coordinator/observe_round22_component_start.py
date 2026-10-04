"""ROOT observes recorded execution metadata only; no mathematical evaluation."""
import hashlib, json
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role6/thermal_h1'
A=P/'actual_component22'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
gate=C/'messages/round22_thermal_component_authorization.json'
assert sha(gate)=='0eb9fef5c1796253b985c331a74b1b557c6dc57ca456c32fd93bef9f4f8b96d5'
start=read(A/'actual_START.json'); captures=read(A/'PREEXEC_captures.json')
prep=read(P/'component_preparation22.json')
assert start['scope']=='THERMAL_COMPONENT_AUX_ONLY' and start['captures_complete']
assert start['gate_sha256']==sha(gate)
assert start['preparation_sha256']==sha(P/'component_preparation22.json')
assert captures['attempt_token']==start['attempt_token']
assert captures['math_started'] is False and len(captures['captures'])==27
expected={r['path']:r['sha256'] for r in prep['bindings']}
expected[str(P/'component_preparation22.json')]=sha(P/'component_preparation22.json')
expected[str(gate)]=sha(gate)
assert {r['source']:r['sha256'] for r in captures['captures']}==expected
for row in captures['captures']:
    assert row['phase']=='PREEXEC' and sha(Path(row['copy']))==row['sha256']
observation={'schema':'ROUND22_COMPONENT_START_METADATA_OBSERVATION_V1',
 'observed_utc':datetime.now(timezone.utc).isoformat(),
 'status':'ACTOR_COMPONENT_ATTEMPT_STARTED_FINAL_VERDICT_NOT_ATTRIBUTED',
 'actor':'ROLE6','actor_command':'f2e59f_session51751',
 'actual_START':start['time_utc'],'attempt_token':start['attempt_token'],
 'start_sha256':sha(A/'actual_START.json'),'PREEXEC_catalog_sha256':sha(A/'PREEXEC_captures.json'),
 'verified_captures':27,'gate_sha256':sha(gate),
 'root_numeric_invocations':0,'root_Lean_invocations':0,
 'global_H1_claim':False,'coefficient_N_claim':False,'D_N_paid':False,'WIN':False}
out=C/'messages/round22_component_start_observation.json'
with out.open('x',encoding='utf-8') as f:
    json.dump(observation,f,ensure_ascii=False,indent=2);f.write('\n')
cp_path=C/'checkpoint.json';cp=read(cp_path)
cp['phase']='ROUND22_H1_COMPONENT_ACTUAL_IN_PROGRESS_FORMAL_AUTHOR_BATCHES_PREPARING'
for actor in cp['in_flight_executors']:
    if actor['role']==6: actor['status']='NEW_COMPONENT_AUX_ACTUAL_STARTED_SINGLE_ATTEMPT_RESULT_NOT_ATTRIBUTED'
cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_component_start_observation.json')
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(observation,indent=2))
