"""ROOT authorizes a frozen auxiliary independent audit; metadata only."""
import hashlib, json
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/judge5'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'batch02_prepared_manifest.json'; m=read(mp)
cat=read(P/'batch02_catalog.json'); receipt=read(P/'batch02_prepared_receipt.json')
assert sha(mp)=='c0a2ef8b8ce38fc2781924d6cdc776177a3b3b4dac121bb1d13a1f01158d04dd'
assert sha(P/'run_judge22_batch02_once.py')==m['launcher_sha256']=='12d14af404639024c0bcc62e6bde114710885997c51511f1694e7579c8beb513'
assert sha(P/'prepare_judge22_batch02.py')=='2c9a24fa0fe3cf1369e88b1781b5e24ecbca4029ee15615cdd1d571ce552deea'
assert sha(P/'batch02_catalog.json')==m['source_catalog_sha256']=='90addad838416c8f36782979e6d2ffac051494ed895b4141d4a2f666a9c13714'
assert sha(P/'batch02_prepared_receipt.json')=='b1cd3e31fd1f1e857bfa6c6691a3e957749cb97c0a2165612c9f21110c50a59d'
assert m['status']==receipt['status']=='PREPARED_SOURCE_ONLY_GATE_CLOSED'
assert m['modules']==['EpsteinUnfold22','EpsteinTail22','GammaPrerequisites22']
assert len(m['immutable_inputs'])==7214 and m['import_module_count']==3568 and not m['unresolved_modules']
assert m['compiler_invocations']==m['mathematical_numeric_invocations']==0
assert not m['author_olean_used'] and not m['win'] and cat['total_declarations']==56
for row in m['immutable_inputs']: assert sha(Path(row['path']))==row['sha256'], row['path']
for row in receipt['artifacts']: assert sha(P/row['file'])==row['sha256'], row['file']
for row in cat['modules']:
    assert sha(Path(row['source']))==sha(Path(row['author_source']))==row['source_sha256']
    assert row['author_provenance']['exit_code']==0 and row['author_provenance']['invocations']==1
for bank in m['numeric_banks']:
    data=read(Path(bank['path']))
    assert sha(Path(bank['path']))==bank['sha256'] and data['status']==bank['status']
    assert len(data['cases'])==bank['case_count']
old=read(P/'batch01_attempt01/receipt.json')
assert old['status']=='INDEPENDENT_BATCH01_AUX_PASS' and old['all_inputs_unchanged']
oldbindings=read(P/'batch02_batch01_bindings.json')
assert len(oldbindings['inputs'])==35 and oldbindings['compiler_invocations']==0
for row in oldbindings['inputs']: assert sha(Path(row['path']))==row['sha256']
archives=read(B/'round22/previous_artifacts_sha256.json')
assert archives['file_count']==3089
for relative, expected in archives['sha256'].items(): assert sha(B/relative)==expected, relative
prior=read(C/'messages/round22_judge5_batch01_authorization.json')
for key,path in [('python_sha256',r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'),('lean_sha256',r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')]: assert sha(Path(path))==prior[key]
assert not (P/'batch02_attempt01').exists()
gate={'schema':'ROUND22_JUDGE5_BATCH02_AUTHORIZATION','created_utc':datetime.now(timezone.utc).isoformat(),'role':'ROLE5','authorized':True,'attempt':'batch02_attempt01','modules':m['modules'],'compiler_invocations_maximum':3,'source_manifest_sha256':sha(mp),'launcher_sha256':m['launcher_sha256'],'python_sha256':prior['python_sha256'],'lean_sha256':prior['lean_sha256'],'numeric_banks':m['numeric_banks'],'numeric_banks_verified':True,'readonly_batch01_dependency_directory':m['batch01_dependency_directory'],'independent_audit':True,'author_olean_allowed':False,'no_win':True,'inputs_verified':7214,'protected_archive_paths_verified':3089,'readonly_batch01_files_verified':35,'root_FULL_reads':{'launcher':'5a3bb5','builder':'2d66a4','catalog':'810621','reads_and_batch01_bindings':'773c55','prepared_receipt_and_preparation':'bffa60','author_Unfold':'976498 actual log and receipt; source prior 8fdf92','author_Tail':'b2b8ef source; 71ee95 actual receipt and log','author_Gamma':'aa39bb source; 3bfaf7 actual receipt and log'},'manifest_scope':'Complete JSON parsed and all 7214 input hashes checked; header projection only, no FULL raw display claim.','root_compiler_invocations':0,'root_numeric_invocations':0,'D_N_paid':False,'WIN':False}
gp=C/'messages/round22_judge5_batch02_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_H1_PRECRITIQUE_JUDGE_BATCH02_THREE_INDEPENDENT_CHILDREN_AUTHORIZED'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_judge5_batch02_authorization.json']
for actor in cp['in_flight_executors']:
    if actor['role']==5: actor['status']='BATCH02_THREE_INDEPENDENT_CHILDREN_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'manifest_header_projection':{k:v for k,v in m.items() if k!='immutable_inputs'},'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':7214,'verified_archives':3089,'root_compiler_invocations':0,'root_numeric_invocations':0,'WIN':False},ensure_ascii=False,indent=2))
