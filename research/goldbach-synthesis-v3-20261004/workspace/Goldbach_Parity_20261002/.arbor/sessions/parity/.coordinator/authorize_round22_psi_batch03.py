"""ROOT byte bindings only for a distinct third author batch."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role3/h1_psi/revision03'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'psi_source_manifest22.json';m=read(mp)
assert sha(mp)=='e69c215fe676eaf5b3a6902d9797a50a7d03f86d5bd9f136aeee378c94bbc43f'
assert sha(P/'psi_prepared_receipt22.json')=='cb98633b3f43e47f66ad161665f4b3994846dd4eeb5d473be08f11dad7c60522'
assert sha(P/'final_read_receipt22.json')=='01b65afad6d67f0092b8a1f626ed6bd02641fb0c6694ed2d109609ca4f2f66c1'
assert sha(P/'run_psi_batch_once22.py')=='14cc89e8afdd600843e276d6bad789e19449041370c883168848ab295848857c'
assert sha(P/'prepare_psi_metadata22.ps1')=='95e17ef463f0db00e6185d10bdc15e52f49f50d9a7cbdbe79cea754829233e33'
assert m['status']=='PREPARED_SOURCE_ONLY' and m['compiler_invocations']==0
assert len(m['inputs'])==65 and m['declarations']==54
assert [r['declaration_count'] for r in m['catalog']]==[19,23,10,2]
assert m['modules']==['GammaPsiCore22','GammaPsiBetaLimit22','GammaPsiIntegral22','GammaPsiDuplication22']
for r in m['inputs']:
    p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],r['path']
for r in m['catalog']:
    assert sha(Path(r['path']))==sha(P/(r['module']+'.lean'))==r['sha256']
    assert len(r['declarations'])==r['declaration_count']
assert sha(P/'source_final/GammaPsiDuplication22.lean')=='8a7f2c014866bfe49814c9310dfc012acd05e87c962b5976a32cf0fec9a2179f'
closure=read(Path(m['cache_closure_path']))
assert sha(Path(m['cache_closure_path']))=='8211d1e3ba1f94f4f415c20a4a26ad12cbd4cdc5a3458a3a8becb17482aac0d6'
assert closure['module_count']==len(closure['nodes'])==3238
assert closure['artifact_count']==len(closure['artifacts'])==6476
assert any(r['module']=='Init' for r in closure['nodes'])
for r in closure['artifacts']:
    p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],r['path']
assert sha(Path(m['python_path']))==m['python_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(Path(m['lean_path']))==m['lean_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
nr=m['numeric_evidence'];assert not nr['numeric_PASS'] and not nr['counterexample_established']
assert sha(Path(nr['receipt_path']))==nr['receipt_sha256']=='2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48'
actual=read(Path(nr['receipt_path']));assert actual['exit_code']==1 and actual['result_sha256'] is None and actual['post_integrity']
assert sha(B/'round22/judge5/batch02_attempt01/GammaPrerequisites22.olean')==m['readonly_gamma_olean_sha256']=='fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477'
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,expected in archives['sha256'].items():assert sha(B/rel)==expected,rel
assert not (P/'psi_batch03_attempt01').exists()
previous=C/'messages/round22_role3_psi_batch02_authorization1.json'
assert sha(previous)=='b59780b8e4ff98647a9f803257cbc07434f12b99a13f04c8250c0a65e04dc6a0'
gate=read(previous)
gate.update({'schema':'ROUND22_ROLE3_H1_PSI_BATCH03_AUTHORIZATION_V1','created_utc':datetime.now(timezone.utc).isoformat(),
 'stage':'H1_PSI_BATCH03','attempt':'psi_batch03_attempt01','source_manifest_sha256':sha(mp),
 'launcher_sha256':sha(P/'run_psi_batch_once22.py'),'verified_inputs':65,
 'root_FULL_reads':{'Core_and_Integral':'0e6adc','Beta':'57a1ec','Duplication_identical_prior':'9802c8',
 'launcher':'77246f','builder':'1a558a','prepared_finalread_receipts':'b77576','preparation_scope_failure02':'f9ac4a'},
 'manifest_scope':'CompleteJSON parsed/all65inputs hashed; no FULL raw manifest/cache/API claim',
 'previous_author_batches_closed_without_PASS':2,'root_compiler_invocations':0,'root_numeric_invocations':0,
 'numeric_observation_scope':'Frozen historical serialization failure; laterR01closedcomponentAUX_PASS does not certify globalH1',
 'new_component_R01_result_sha256':'c43622616022e65991aee5a12d189d3bae142db1f2d347cb131e8abd685c7a6c'})
gp=C/'messages/round22_role3_psi_batch03_authorization1.json'
with gp.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json';cp=read(cpp)
cp['phase']='ROUND22_PSI_BATCH03_FOUR_AUTHOR_CHILDREN_AUTHORIZED_JUDGE_GAMMA_DERIVATIVE_PREPARING'
for a in cp['in_flight_executors']:
    if a['role']==3:a['status']='PSI_BATCH03_FOUR_AUTHOR_CHILDREN_AUTHORIZED_NOT_STARTED'
    if a['role']==5:a['status']='BATCH03_GAMMA_DERIVATIVE_ONE_NEW_INDEPENDENT_CHILD_PREPARING'
    if a['role']==4:a['status']='ANALYTIC_BATCH02_FOUR_REMAINING_SOURCE_PREPARING_DEP_JUDGE_PENDING'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'inputs_verified':65,'cache_artifacts_verified':6476,
 'archives_verified':3089,'root_math_invocations':0,'root_compiler_invocations':0,'WIN':False},indent=2))
