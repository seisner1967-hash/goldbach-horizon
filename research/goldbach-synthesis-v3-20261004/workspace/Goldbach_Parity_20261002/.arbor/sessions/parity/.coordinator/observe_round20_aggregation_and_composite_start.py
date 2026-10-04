"""Byte/receipt observation only: no numeric or compiler execution."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
W=B/'round20/role4'
path=W/'aggregation_build_receipt.json'
assert sha(path)=='0a817e718c280060b086aa7def75fac6afbd7edafd467afc42a9b1173398e5a1'
ledger=load(path)
assert [x['exit_code'] for x in ledger['attempts']]==[1,0]
assert [x['credited_pass'] for x in ledger['attempts']]==[False,True]
attempts=[]
for x in ledger['attempts']:
    assert x['phase']=='FINISHED' and x['post_integrity']['all_unchanged']
    assert not x['post_integrity']['failed_bindings']
    for k in ['snapshot','builder_snapshot','started_receipt','log']:
        assert sha(x[k])==x[k+'_sha256']
    started=load(x['started_receipt'])
    assert started['source_sha256']==x['source_sha256']==x['snapshot_sha256']
    assert started['command']==x['command'] and started['started_utc']==x['started_utc']
    if x['olean']: assert sha(x['olean'])==x['olean_sha256']
    for label,check in x['post_integrity']['checks'].items():
        assert check['unchanged'] and check['actual_sha256']==check['expected_sha256']
        if label!='source': assert sha(check['path'])==check['expected_sha256'],label
    attempts.append({k:x[k] for k in ['attempt','started_utc','finished_utc','exit_code','credited_pass','source_sha256','snapshot_sha256','log_sha256','olean_sha256']})
imports={}
for lname in ['build_receipt.json','extension_build_receipt.json','aggregation_build_receipt.json']:
    for module in load(W/lname)['successful_modules'].values():
        for k in ['source','olean']:
            assert sha(module[k])==module[k+'_sha256']
            imports[str(Path(module[k]).relative_to(B)).replace('\\','/')]=module[k+'_sha256']
assert len(imports)==16
obs={'round':20,'role':4,'at_utc':datetime.now(timezone.utc).isoformat(),
     'ledger_sha256':sha(path),'actual_aggregation_attempts':attempts,
     'all_actual_author_attempts':20,'author_pass_count':8,'technical_fail_count':12,
     'frozen_new_import_bindings':imports,'FULL_actual_logs_and_current_source':'527549',
     'root_lean_executions':0,'root_mathematical_executions':0,'source_budget_proved':False,'victory':False}
obs_path=C/'messages/round20_formal4_phase4_root_observation.json'
save(obs_path,obs)
V=B/'round20/role6_composite/canonical_attempt01'
start=load(V/'started.json'); manifest=load(V/'input_manifest.json')
assert start['round']==20 and start['attempt']==1 and start['node']=='13.12'
assert sha(V/'input_manifest.json')==start['input_manifest_sha256']
assert manifest['all_captures_before_child_start'] and manifest['phase']=='PREEXEC'
assert manifest['bindings']==start['captures_preexec'] and len(manifest['bindings'])==33
for label,item in manifest['bindings'].items():
    assert sha(item['original'])==item['sha256']==sha(item['snapshot']),label
assert sha(start['runtime'])==start['runtime_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(start['root_authorization_path'])==start['root_authorization_sha256']=='7d1f238ddd3667547e8ff375c41fb7cc10db356b6e400874890bdf85f3e88adf'
assert Path(start['subprocess_command'][-1]).resolve()==(V/'inputs/composite_checks.py').resolve()
start_obs={'round':20,'role':6,'node':'13.12','observed_at_utc':datetime.now(timezone.utc).isoformat(),
           'actual_started_at_utc':start['started_at_utc'],'started_sha256':sha(V/'started.json'),
           'manifest_sha256':sha(V/'input_manifest.json'),'capture_count':33,
           'all_original_and_snapshot_bytes_verified':True,'receipt_exists_at_observation':(V/'receipt.json').exists(),
           'root_numeric_or_sign_recomputation':0,'root_lean_executions':0,'victory':False}
start_obs_path=C/'messages/round20_composite_start_root_observation.json'
save(start_obs_path,start_obs)
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_EIGHT_FROZEN_FRIABLE_AUTHOR_PASSES_COMPOSITE_UNIQUE_REAL_RUN_GEOMETRY_PREEXEC'
for item in cp['in_flight_executors']:
    if item['role']==4:item['status']='EIGHT_FROZEN_PASSES20_ACTUAL_ATTEMPTS_SOURCE_GEOMETRY_AND_BUDGET_PENDING'
    if item['role']==6:item['status']='FRIABLE_FINAL_CLOSED_COMPOSITE_CANONICAL_ATTEMPT01_REAL_START33_VERIFIED'
cp['last_progress']+=' Aggregation real[1,0] FULL527549/stdaxioms/16frozenimports verified; eight author PASSes20actual attempts. Composite realSTART03:52:38Z/33PREEXEC current+snapshot bytes verified, no finish assumed. Geometry preEXEC; root math0/noWin.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'aggregation_observation_sha256':sha(obs_path),'composite_start_observation_sha256':sha(start_obs_path),
                  'eight_passes':True,'actual_author_attempts':20,'composite_capture_count':33,'root_math':0,'victory':False}))
