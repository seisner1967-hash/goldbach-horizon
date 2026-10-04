"""Authorize frozen independent audit; only metadata/producer status checks here."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/judge5'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'batch01_prepared_manifest.json'; m=read(mp); cat=read(P/'batch01_catalog.json'); r=read(P/'batch01_prepared_receipt.json')
assert sha(mp)==r['manifest_sha256']=='ef7f18133f8e78887088b8dc5cc3da5d3830a5574424ca6f5a2d087cd55b3c82'
assert sha(P/'run_judge22_batch01_once.py')==r['launcher_sha256']=='1b00387f58d4c2daf8e1a832494014ea44b8f7b2bb39802578b44ca94e2ea7cc'
assert sha(P/'batch01_catalog.json')==m['source_catalog_sha256']==r['source_catalog_sha256']=='f162256f9a181d2d30eb8d813ce58e283c6c942fa05b369cbf0f25b53827632d'
assert m['status']=='PREPARED_SOURCE_ONLY_GATE_CLOSED' and len(m['immutable_inputs'])==7112 and m['import_module_count']==3541 and not m['unresolved_modules']
assert m['compiler_invocations']==m['mathematical_numeric_invocations']==0 and not m['author_olean_used_by_judge'] and not m['win']
assert m['modules']==['EpsteinKernel22','EpsteinFinite22'] and cat['total_declarations']==51
for e in m['immutable_inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
for e in cat['modules']:
    assert sha(Path(e['source']))==sha(Path(e['author_source']))==e['source_sha256']
    ar=read(Path(e['author_receipt'])); assert ar['status']=='AUTHOR_STAGE_AUX_PASS' and ar['rows'][0]['exit_code']==0
numeric=B/'round22/role6/actual_epstein22/epstein_result22.json'; nr=read(numeric)
assert sha(numeric)=='e9e72edeaf787644aa6a0f341992ec82270428d14e876ac4b7be00d5cc3e508a' and nr['status']=='EPSTEIN_UNFOLDING_AUX_PASS'
prior=read(C/'messages/round22_role3_stage03_attempt03_authorization.json')
for key,path in [('python_sha256',r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'),('lean_sha256',r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')]: assert sha(Path(path))==prior[key]
assert not (P/'batch01_attempt01').exists()
gate={'schema':'ROUND22_JUDGE5_BATCH01_AUTHORIZATION','created_utc':datetime.now(timezone.utc).isoformat(),'role':'ROLE5','authorized':True,'attempt':'batch01_attempt01','modules':m['modules'],'compiler_invocations_maximum':2,'source_manifest_sha256':sha(mp),'launcher_sha256':r['launcher_sha256'],'python_sha256':prior['python_sha256'],'lean_sha256':prior['lean_sha256'],'numeric_verdict':nr['status'],'numeric_bank_path':str(numeric),'numeric_bank_sha256':sha(numeric),'numeric_bank_verified':True,'independent_audit':True,'author_olean_allowed':False,'no_win':True,'inputs_verified':7112,'root_FULL_reads':{'launcher':'7fe363','builder':'4073d1','catalog':'647f9b','reads':'fe095e','prepared_receipt':'4e02f4','source_audit':'3cfeec','author_Kernel_source':'1d6a2f','author_Finite_source':'80588c'},'manifest_scope':'Complete JSON parsed and 7112 bytes verified; header projection only, not FULL display.','root_compiler_invocations':0,'D_N_paid':False,'WIN':False}
gp=C/'messages/round22_judge5_batch01_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_JUDGE_BATCH01_TWO_INDEPENDENT_CHILDREN_AUTHORIZED_UNFOLD_AUTHOR_PENDING'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_judge5_batch01_authorization.json']
for actor in cp['in_flight_executors']:
    if actor['role']==5: actor['status']='BATCH01_TWO_INDEPENDENT_CHILDREN_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'manifest_HEADER_projection':{k:v for k,v in m.items() if k!='immutable_inputs'},'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':7112,'root_compiler_invocations':0,'WIN':False},ensure_ascii=False,indent=2))
