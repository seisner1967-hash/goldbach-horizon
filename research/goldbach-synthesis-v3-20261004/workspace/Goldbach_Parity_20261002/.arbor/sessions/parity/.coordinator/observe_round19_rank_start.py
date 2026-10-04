"""Root verifies an actual recorded START; no producer call or output check."""
import json,hashlib,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round19/role6_rank/canonical_attempt01'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert len(sys.argv)==2
p=A/'started.json'; assert sha(p)==sys.argv[1]
s=read(p); auth=read(C/'messages/round19_rank_authorization.json')
assert s['launcher_command']==auth['exact_authorized_command']
assert s['root_authorization']==auth['authorization']
assert s['round']==19 and s['node']=='13.11' and s['attempt']==1
assert s['python_sha256']==sha(Path(s['subprocess_command'][0]))=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert s['cwd']==str(A) and s['subprocess_command'][4]==str(A/'inputs/producer.py')
manifest=read(A/'inputs/input_manifest.json')
assert sha(A/'inputs/input_manifest.json')==s['input_manifest_sha256']
assert manifest['captures']==s['PREEXEC_captures'] and len(manifest['captures'])==13
for name,item in manifest['captures'].items():
    snap,original=Path(item['snapshot']),Path(item['original'])
    assert snap.is_relative_to(A/'inputs') and original.is_relative_to(B)
    assert sha(snap)==item['sha256'] and snap.stat().st_size==item['bytes'],name
    assert sha(original)==item['sha256'],name
assert s['environment_changes']['ROOT19_RANK_PREEXEC_GATE']==auth['authorization']
assert s['environment_changes']['PYTHONDONTWRITEBYTECODE']=='1'
assert s['environment_changes']['PYTHONUTF8']=='1'
assert s['W_D_kernel_parent_or_old_preflight_Lean_PDF_execution'] is False
observation={
 'status':'ROOT_VERIFIED_ACTUAL_UNIQUE_NEW_RANK19_START',
 'observed_at_utc':datetime.now(timezone.utc).isoformat(),
 'actual_start':s['started_at_utc'],'started_receipt_sha256':sha(p),
 'input_manifest_sha256':s['input_manifest_sha256'],'PREEXEC_captures_verified':13,
 'command':s['subprocess_command'],'root_math_and_Lean_invocations':0,
 'result_not_yet_inspected':True,'victory':False}
out=C/'messages/round19_rank_start_root_observation.json'
with out.open('x',encoding='utf-8') as f: f.write(json.dumps(observation,ensure_ascii=False,indent=2)+'\n')
cp_path=C/'checkpoint.json'; cp=read(cp_path)
cp['phase']='ROUND19_NEW_RANK_ACTUAL_STARTED_ROLE4_COMPILES_JUDGE_PREPARING'
for row in cp['in_flight_executors']:
    if row['role']==6: row['status']='actual_unique_NEW_rank19_started_nonSS_FINAL_gel_no_replay'
cp['last_progress']+=' NEW all-rank13.11 fullcurrent four code sources/contract/preparation fullyread+SHAverified12bindings; root distinct unique authorization issued. ActualcanonicalSTART independentlyverified13PREEXEC captures/runtime/cwd/commands, completionnotyetinspected. Complete12m candidate domain, every admissible conductor inclA0, true theta/rawPP and all reference/unit/rank/ordinaryintervalAP prices retained. No source/BV onset applied. One transient root readonly process ACL-setup failure resolved by read retry, no producer failure. OfficialJudge30/507 unchanged; noWin.'
for rel in [
 '.arbor/sessions/parity/.coordinator/messages/round19_rank_authorization.json',
 'round19/role6_rank/canonical_attempt01/started.json',
 '.arbor/sessions/parity/.coordinator/messages/round19_rank_start_root_observation.json']:
    if rel not in cp['previous_goal_turn_evidence']: cp['previous_goal_turn_evidence'].append(rel)
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(observation,ensure_ascii=False,indent=2))
