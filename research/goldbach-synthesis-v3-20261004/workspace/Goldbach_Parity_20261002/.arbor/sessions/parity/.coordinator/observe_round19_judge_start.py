"""Observe the actual canonical Judge START via existing metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); J=B/'round19/judge'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
start=read(J/'audit_started.json'); inputs=read(J/'input_manifest.json')
assert start['phase']=='PREEXEC' and start['root_authorization']=='ROOT19_JUDGE_CANONICAL_ATTEMPT01'
assert inputs['status']=='FROZEN_PREEXEC_AFTER_EXPLICIT_ROOT_GATE'
assert sha(J/'authorization.json')==start['authorization_sha256']=='6da21513c45dac50c777390ffb8d55f0dd3b87c3a5f59ff81e82b2603dd07c3e'
assert sha(J/'preparation.json')==start['preparation_sha256']=='4763b4463708b6458186cd9872c94010c055487443801915e7fd487e307c7dae'
assert sha(J/'input_manifest.json')==start['input_manifest_sha256']
assert sha(J/'audit.py')==start['audit_source_sha256']==inputs['judge_code_sha256']['audit.py']
assert sha(J/'run_once.py')==start['launcher_sha256']==inputs['judge_code_sha256']['run_once.py']
assert sha(Path(start['python_executable']))==start['python_sha256']==inputs['python_sha256']
assert sha(Path(start['lean_executable']))==start['lean_sha256']==inputs['lean_sha256']
assert start['command']==[start['python_executable'],'-B','-X','utf8',str(J/'audit.py')]
assert start['cwd']==str(J) and len(start['PREEXEC_captures'])==15
for name,row in start['PREEXEC_captures'].items():
    assert sha(Path(row['original']))==sha(Path(row['snapshot']))==row['sha256'],name
assert start['PREEXEC_captures']==inputs['PREEXEC_captures']
assert not start['old_producer_Lean_kernel_PDF_executed']
obs={'status':'ROOT_OBSERVED_ACTUAL_UNIQUE_JUDGE19_START_RESULT_NOT_YET_VERIFIED',
 'observed_utc':datetime.now(timezone.utc).isoformat(),
 'actual_started_utc':start['started_at_utc'],'command':start['command'],'cwd':start['cwd'],
 'start_sha256':sha(J/'audit_started.json'),'input_manifest_sha256':sha(J/'input_manifest.json'),
 'PREEXEC_captures_verified':15,'new_modules_authorized':11,
 'root_audit_compiler_numeric_invocations':0,'victory':False}
with (C/'messages/round19_judge_start_root_observation.json').open('x',encoding='utf-8') as f:
    f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND19_ACTUAL_UNIQUE_INDEPENDENT_JUDGE_RUNNING'
cp['last_progress']+=' Actual uniqueJudge19 START '+start['started_at_utc']+' rootobserved15PREEXEC/runtime/command/inputgel; real completion not yetverified. Official30/507 unchanged,noWin.'
for row in cp['in_flight_executors']:
    if row['role']==5: row['status']='actual_unique_independent_audit_running_result_not_yet_verified'
cp['previous_goal_turn_evidence']+=['round19/judge/audit_started.json','.arbor/sessions/parity/.coordinator/messages/round19_judge_start_root_observation.json']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
