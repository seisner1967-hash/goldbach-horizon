"""ROOT metadata gate for four new author Lean modules; no math or compiler call."""
import hashlib, json
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/role3/h1_psi'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'psi_source_manifest22.json';m=read(mp)
assert sha(mp)=='3403b51391a8ccba3578d100533615dfdd8dd1ce08560bbe7f419cde39a0c253'
assert sha(P/'psi_prepared_receipt22.json')=='9dedf9019ef32ace6af93066ba975e250f8a47de5c35f567d4bc8b671f15dea6'
assert sha(P/'run_psi_batch_once22.py')=='9710c4c3bb149550e07a2311d4ed555803ac79c4db89d7f19de35bd3cbafe8ed'
assert sha(P/'prepare_psi_metadata22.ps1')=='9fc790a48e29e8b0257b4f21ea93eae912c1d260a6752f2a39be6c08e7402bef'
assert m['status']=='PREPARED_SOURCE_ONLY' and m['role']=='ROLE3' and m['node_id']=='15.3'
assert m['modules']==['GammaPsiCore22','GammaPsiBetaLimit22','GammaPsiIntegral22','GammaPsiDuplication22']
assert [r['declaration_count'] for r in m['catalog']]==[19,23,10,2] and m['declarations']==54
assert len(m['inputs'])==47 and m['compiler_invocations']==0
assert not m['C5_paid'] and not m['global_H1_paid'] and not m['D_N_paid'] and not m['victory']
for row in m['inputs']:
    p=Path(row['path']);assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row['path']
for row in m['catalog']:
    assert sha(Path(row['path']))==row['sha256']
    assert sha(P/(row['module']+'.lean'))==row['sha256']
    assert len(row['declarations'])==row['declaration_count']
assert sha(Path(m['python_path']))==m['python_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(Path(m['lean_path']))==m['lean_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
assert sha(Path(m['cache_closure_path']))=='cfc7b4578a92333b779b495eb7fd35a675b843bf8018f8536c877a925d688c41'
closure=read(Path(m['cache_closure_path']))
assert closure['module_count']==len(closure['nodes'])==m['cache_closure_module_count']==3238
assert closure['artifact_count']==len(closure['artifacts'])==m['cache_closure_artifact_count']==6476
assert closure['scope']=='STATIC_IMPORT_HEADER_PARSE_AND_FILE_HASH_ONLY_NO_LEAN_PROBE'
assert any(r['module']=='Init' for r in closure['nodes'])
for row in closure['artifacts']:
    p=Path(row['path']);assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row['path']
numeric=m['numeric_evidence'];receipt=read(Path(numeric['receipt_path']))
assert sha(Path(numeric['receipt_path']))==numeric['receipt_sha256']=='2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48'
assert receipt['exit_code']==1 and receipt['result_sha256'] is None and receipt['post_integrity']
assert not numeric['numeric_PASS'] and not numeric['counterexample_established']
gamma=B/'round22/judge5/batch02_attempt01/GammaPrerequisites22.olean'
assert sha(gamma)==m['readonly_gamma_olean_sha256']=='fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477'
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for relative,expected in archives['sha256'].items():assert sha(B/relative)==expected,relative
assert not (P/'psi_batch01_attempt01').exists()
gate={'schema':'ROUND22_ROLE3_H1_PSI_BATCH01_AUTHORIZATION_V1',
 'created_utc':datetime.now(timezone.utc).isoformat(),'role':'ROLE3','node_id':'15.3',
 'stage':'H1_PSI_BATCH01','attempt':'psi_batch01_attempt01','authorized':True,'modules':m['modules'],
 'numeric_pass_required':False,'numeric_PASS':False,'numeric_counterexample_established':False,
 'numeric_receipt_sha256':numeric['receipt_sha256'],'numeric_receipt_exit_code':1,
 'source_manifest_sha256':sha(mp),'launcher_sha256':sha(P/'run_psi_batch_once22.py'),
 'python_sha256':m['python_sha256'],'lean_sha256':m['lean_sha256'],'no_win':True,
 'readonly_gamma_olean_sha256':m['readonly_gamma_olean_sha256'],
 'compiler_invocations_maximum':4,'stop_first_failure':True,'retry_count':0,
 'verified_inputs':47,'verified_cache_artifacts':6476,'verified_cache_modules':3238,
 'cache_read_scope':'Complete JSON parsed and all bytes hashed; no FULL API or FULL raw closure claim',
 'protected_archives_verified':3089,'root_numeric_invocations':0,'root_compiler_invocations':0,
 'root_FULL_reads':{'manifest':'21ca68','receipt':'4d3810','launcher':'e18d94','builder':'37d6c9',
   'preparation':'399308','API_inventory':'b48356','scope':'ee7a64','Core':'d611f6',
   'Beta_final':'e21bc8','Integral':'99bfe7','Duplication':'623693','C5_next':'0c5ab8'},
 'source_mathematical_review_owner':'ROLE3 author and ROLE4 SOURCE review a84072/41e749; no independent elaboration claim',
 'global_H1_paid':False,'C5_paid':False,'D_N_paid':False,'WIN':False}
gp=C/'messages/round22_role3_psi_batch01_authorization1.json'
with gp.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
cp_path=C/'checkpoint.json';cp=read(cp_path)
cp['phase']='ROUND22_H1_PSI_FOUR_AUTHOR_CHILDREN_AUTHORIZED_ANALYTIC_AND_NUMERIC_REVISION_PREPARING'
for actor in cp['in_flight_executors']:
    if actor['role']==3:actor['status']='H1_PSI_BATCH01_FOUR_AUTHOR_CHILDREN_AUTHORIZED_NOT_STARTED'
cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_role3_psi_batch01_authorization1.json')
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'inputs_verified':47,'cache_artifacts_verified':6476,
 'archives_verified':3089,'root_math_executions':0,'root_compiler_executions':0,'WIN':False},indent=2))
