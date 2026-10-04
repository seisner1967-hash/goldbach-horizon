"""Verify actual new producer START and immutable inputs; metadata only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';A=B/'round19/role6_nonss/canonical_attempt01'
def read(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
out=C/'messages/round19_nonss_start_root_observation.json'
assert not out.exists()
p=A/'started.json'
assert digest(p)=='a5704847edb1d2e1b0d9a88e9441814a6634cc95d5d2a0bea8e1a77c9e94c34b'
s=read(p);auth=read(C/'messages/round19_nonss_authorization.json')
assert s['launcher_command']==auth['new_command_authorized']
assert s['root_authorization']==auth['token'] and s['round']==19 and s['node']=='14.4'
assert s['python_sha256']==digest(Path(s['subprocess_command'][0]))=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert s['cwd']==str(A) and s['subprocess_command'][4]==str(A/'inputs/producer.py')
assert digest(A/'inputs/input_manifest.json')==s['input_manifest_sha256']
manifest=read(A/'inputs/input_manifest.json')
assert manifest['captures']==s['PREEXEC_captures'] and len(manifest['captures'])==13
for name,item in manifest['captures'].items():
    snap=Path(item['snapshot']);orig=Path(item['original'])
    assert snap.is_relative_to(A/'inputs') and orig.is_relative_to(B)
    data=snap.read_bytes()
    assert sha256(data).hexdigest()==item['sha256'] and len(data)==item['bytes'],name
    assert digest(orig)==item['sha256'],name
assert s['environment_changes']['PYTHONDONTWRITEBYTECODE']=='1'
assert s['environment_changes']['PYTHONUTF8']=='1'
assert s['environment_changes']['ROOT19_NONSS_PREEXEC_GATE']==auth['token']
receipt=dict(status='ROOT_VERIFIED_ACTUAL_UNIQUE_NEW_NONSS19_START',observed_utc=datetime.now(timezone.utc).isoformat(),
 started_at_utc=s['started_at_utc'],started_receipt_sha256=digest(p),actual_command=s['subprocess_command'],
 input_manifest_sha256=s['input_manifest_sha256'],PREEXEC_capture_bindings=13,
 actual_canonical_starts_observed=1,producer_executions_by_root=0,Lean_invocations=0,
 completion_result_not_inspected=True,no_old_math_or_Lean_execution=True,victory=False)
out.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp['phase']='ROUND19_NONSS_ACTUAL_CANONICAL_STARTED_FORMAL_SOURCES_RANK_BANK_PREPARING'
cp['last_progress']+=' ActualuniqueNEWnonSS19 started00:15:27.314820UTC, commandcapturedproducer and13PREEXECinputs/hash/runtime independentlyobservedroot; resultnotyetinspected. R6preparingsecond13.11bank, formal4fivesourcesREADY/0Lean; noWin/no oldmath executed.'
for role in cp['in_flight_executors']:
    if role['role']==6:role['status']='actual_uniqueNEWnonSS19_started_second13.11bank_preparing'
    if role['role']==4:role['status']='five_new_sources_READY_still0Lean_waiting_canonicalPASS_gate'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+[
 'round19/role6_nonss/canonical_attempt01/started.json',
 '.arbor/sessions/parity/.coordinator/messages/round19_nonss_start_root_observation.json',
 '.arbor/sessions/parity/.coordinator/messages/round19_eval_metadata_FAILED01.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('ActualuniqueNEWnonSS19 START verified13captures/runtime/command; rootmetadataonly, no math/Lean/Win')
