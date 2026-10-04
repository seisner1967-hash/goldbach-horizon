"""Verify actual new preflight19 evidence as metadata; never execute its code."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json, os, re
B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R = B/'round19'; C = B/'.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_bytes())
def h(p):
    q = sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):q.update(block)
    return q.hexdigest()
expected = {'conservation.py':'ee961e35f5d804d2316ce3ae0f705f69c98db258742075c05434167141fa39a4',
    'role6/run_conservation_once.py':'5825758c22ad3f3aa978bd530b5bd0a066c0bb2932ccccef192ef7cfb0c1d7cd',
    'previous_artifacts_sha256.json':'8c0abf930ee8c47b64d335ed286af4566fc674b573216f82f12b05c4ec877150',
    'PROBE_BLOCK.md':'5f9e429bc264002044da60139f3942e7c3de909116d41e6cc52f70afb9a5a12d',
    'conservation.json':'d8bc065d0478dc22070538cbb095b6ab99d8de6844309779f4c882938335b4fe',
    'role6/conservation_attempt01.log':'4640da4ae256cd2da87ec0c1b0272e955423edf8239ce647d3e58c82db4df724',
    'role6/conservation_attempt01_receipt.json':'7798bb5d1ec915ddb76aa61adb8532742208a04a29b80b7ad36399a094049e1a',
    'role6/conservation_attempt01_started.json':'3562760496a0acfa89689996bd28d296c9efb4397040a429431c9473f5f9ffda'}
for name,value in expected.items(): assert h(R/name)==value,name
registry=read(R/'previous_artifacts_sha256.json'); result=read(R/'conservation.json'); receipt=read(R/'role6/conservation_attempt01_receipt.json')
assert read(R/'role6/conservation_attempt01.log') == result
assert (R/'role6/conservation_attempt01.log').read_bytes().replace(b'\r\n',b'\n') == (R/'conservation.json').read_bytes()
assert h(R/'role6/conservation_final_receipt.json') == 'e647e21e5512c48d34c818c9942bb312d172524682b361552c52422fd3c15c53'
final = read(R/'role6/conservation_final_receipt.json')
assert final['status'] == 'FINAL_PREFLIGHT19_PASS_FROZEN_NO_MATHEMATICS' and final['actual_exit_code'] == 0
assert final['actual_new_preflight_subprocess_count'] == 1 and final['capture_count'] == 6
assert final['bound_new_files'] == len(final['new_file_sha256']) == 14
for name,value in final['new_file_sha256'].items(): assert h(R/name) == value,name
assert result['status']=='PASS_EXACT_CONSERVATION' and receipt['exit_code']==0 and receipt['subprocess_launch_error'] is None
assert receipt['started_at_utc']=='2026-10-02T23:24:58.667220+00:00' and receipt['finished_at_utc']=='2026-10-02T23:25:00.862209+00:00'
assert result['expected_file_count']==result['actual_file_count']==result['checked_sha256_count']==registry['file_count']==len(registry['sha256'])==1361
assert all(result[k]==[] for k in ['missing','extra','changed','original_mismatches'])
assert result['observed_sha256']==registry['sha256']
previous=read(B/'round18/previous_artifacts_sha256.json')['sha256']; controller=read(B/'round18/controller_manifest.json')
extra=dict(controller['bindings_sha256']); extra['round18/controller_manifest.json']=h(B/'round18/controller_manifest.json')
assert len(previous)==997 and len(extra)==364 and not set(previous)&set(extra)
assert registry['sha256']==dict(previous,**extra)
for name,value in registry['sha256'].items(): assert h(B/name)==value,name
names=[]
for current,dirs,files in os.walk(B):
    dirs[:]=[d for d in dirs if d not in {'.git','.lake','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'} and not(Path(current)==B and re.fullmatch(r'round\d+',d) and int(d[5:])>=19)]
    names += [p.relative_to(B).as_posix() for f in files if (p:=Path(current)/f)!=B/'REPORT.md']
assert sorted(names)==result['exact_inventory_names']==sorted(registry['sha256'])
assert len(receipt['captures_preexec'])==6
for item in receipt['captures_preexec'].values():
    assert h(Path(item['original']))==h(Path(item['snapshot']))==item['sha256']
    assert Path(item['snapshot']).stat().st_size==item['bytes']
assert h(Path(receipt['python_executable']))==receipt['python_sha256']
assert h(Path(receipt['log']))==receipt['log_sha256'] and h(Path(receipt['result']))==receipt['result_sha256']
assert h(R/'role6/conservation_attempt01_started.json')==receipt['started_receipt_sha256']
for name,item in result['originals'].items(): assert h(Path(name))==item['sha256']==item['expected'] and item['equal']
assert result['historical_union']==dict(previous=997,round18_files=363,controller18=1,total=1361)
assert not result['mathematical_execution'] and not receipt['old_preflights_or_mathematics_executed']
assert result['old_preflight_executions']==result['bank_W_D_log_sign_Lean_PDF_executions']==result['protected_files_written']==0
obs=dict(status='ROOT_VERIFIED_ACTUAL_UNIQUE_CONSERVATION19',observed_at_utc=datetime.now(timezone.utc).isoformat(),
    protected_files=1361,union997_plus364=True,result_log_JSON_identical=True,result_sha256=expected['conservation.json'],
    actual_exit_code=0,actual_started_utc=receipt['started_at_utc'],actual_finished_utc=receipt['finished_at_utc'],PREEXEC_captures=6,preflight_final_bindings=14,
    original_PDF_ZIP_hashes_verified=True,root_executed_preflight_or_math_or_Lean=False,nodes_selected=False,victory=False)
dest=C/'messages/round19_conservation_root_observation.json';assert not dest.exists()
dest.write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p);cp['phase']='ROUND19_CONSERVATION_PASS_TWO_IDEATIONS_ACTIVE'
for item in cp['in_flight_executors']:
    if item['role']==6:item['status']='actual_unique_preflight19_PASS_awaiting_new_concept_numeric_gate'
cp['last_progress'] += ' Actual unique19 byte preflight exit0 at23:25:00.862209UTC,1361 exact inventory/hashes/originals and6 PREEXEC captures; rootfullyread code/launcher/start/receipt and metadata independently verifies997+364/currentinventory/results without runningpreflight. Two substantive ideations active;19node/bank/Lean not selected. NoWin.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round19/conservation.py','round19/conservation.json','round19/role6/conservation_attempt01_receipt.json','.arbor/sessions/parity/.coordinator/messages/round19_conservation_root_observation.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs))
