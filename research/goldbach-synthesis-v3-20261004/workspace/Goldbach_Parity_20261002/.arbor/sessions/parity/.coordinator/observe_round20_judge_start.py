"""Read actual Judge20 START and copied bytes; no audit or compiler invocation."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';J=B/'round20/judge'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
started=load(J/'audit_started.json');inputs=load(J/'input_manifest.json')
assert started['phase']=='PREEXEC' and started['authorization']=='ROOT20_JUDGE_AUTHORIZED'
assert started['input_manifest_sha256']==sha(J/'input_manifest.json')=='c37af3ac54572855e80a124f1f4f733997fbd61a6d7152be3205522e7b2c4305'
assert started['authorization_sha256']==inputs['authorization_sha256']==sha(J/'authorization.json')=='a321f065d36d8d18529d12356d2502e12a75e78fd87a59effeb6db562fba7c03'
assert started['preparation_sha256']==sha(J/'preparation.json')=='fe440243022cf4111c61827f7b6a387e4a2182cd3523b4aef41ae411abcda6a7'
assert inputs['status']=='FROZEN_PREEXEC_AFTER_ROOT_GATE'
assert started['PREEXEC_captures']==inputs['PREEXEC_captures']
assert len(inputs['PREEXEC_captures'])==21
captures={}
for label,record in inputs['PREEXEC_captures'].items():
    assert sha(record['original'])==sha(record['snapshot'])==record['sha256'],label
    captures[label]=record['sha256']
assert started['command']==[inputs['python_executable'],'-B','-X','utf8',str(J/'audit.py')]
assert not started['old_math_Lean_producer_PDF_executed']
first=load(J/'OddBonferroniArithmetic_started.json')
assert first['module']=='OddBonferroniArithmetic' and first['phase']=='PREEXEC'
assert sha(first['source_original'])==sha(first['source'])==sha(first['source_capture'])==first['source_sha256']==first['source_capture_sha256']
assert Path(first['source']).parent==J/'audit'
assert first['input_manifest_sha256']==started['input_manifest_sha256']
assert first['authorization_sha256']==started['authorization_sha256']
assert first['fresh_imports_sha256']=={}
for folder in first['LEAN_PATH'].split(';'):
    assert not any(Path(folder).resolve().is_relative_to((B/'round20'/owner).resolve()) for owner in ['role3','role4','role4_geometry'])
obs={'status':'ROOT_OBSERVED_ACTUAL_JUDGE20_START_FIRST_FRESH_LEAN_STARTED',
 'observed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_started_utc':started['started_utc'],
 'actor_exec_observation':'eb7bfc/session57186','actual_command':started['command'],'actual_cwd':started['cwd'],
 'audit_started_sha256':sha(J/'audit_started.json'),'input_manifest_sha256':sha(J/'input_manifest.json'),
 'authorization_sha256':started['authorization_sha256'],'preparation_sha256':started['preparation_sha256'],
 'all21_PREEXEC_capture_hashes_verified':captures,'first_fresh_Lean_module':first['module'],
 'first_Lean_started_sha256':sha(J/'OddBonferroniArithmetic_started.json'),
 'author20_oleans_in_path':False,'Judge_finish_observed':False,
 'root_mathematical_compiler_audit_invocations':0,'root_numeric_sign_or_log_recomputations':0,'victory':False}
dest=C/'messages/round20_judge_start_root_observation.json'
with dest.open('x',encoding='utf-8',newline='\n') as f:json.dump(obs,f,ensure_ascii=False,indent=2);f.write('\n')
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_ACTUAL_INDEPENDENT_JUDGE_RUNNING_FRESH_SIXTEEN_MODULES'
for row in cp['in_flight_executors']:
    if row['role']==5:row['status']='ACTUAL_UNIQUE_AUDIT_STARTED_04_42_00_UTC_FRESH_LEAN_RUNNING'
cp['last_progress']+=' ActualJudge20 eb7bfc START04:42:00.888897UTC observed/inputc37af3/gatea321/prepfe440/21PREEXECbytes; actualfirstOddBonferroni freshcompile excludesallauthor20paths. Rootnoaudit/compiler/math;16finalcountsnotcreditedyet,noWin.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'root_start_observation':str(dest),'sha256':sha(dest),'actual_start':started['started_utc'],'PREEXEC_checked':21,'root_math':0,'victory':False}))
