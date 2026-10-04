"""Pure ROOT metadata gate for three new author modules; Core is readonly."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role3/h1_psi/revision04'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'psi_source_manifest22.json';m=read(mp)
for name,digest in {'psi_source_manifest22.json':'634c8784597b029946c5ee012d5ec56df95768e8ec9b428fed777434caa79ebb',
 'run_psi_batch_once22.py':'86232c4a95bb5e78ab8057c5e7ce5bb066c205c337340253f0a668e43c85da89',
 'prepare_psi_metadata22.ps1':'900c19c1cd42a753927b2841818f934e4cc024cfc0ab0d0e829342ba8571ee67',
 'psi_prepared_receipt22.json':'d6cbda7474e23d4bfcc44cb579de1f97aa9b8c33909f23b849bfef6c1f171cc9',
 'final_read_receipt22.json':'036ae630597019c1b64215a8122d732dded0c4f83213310e669c7c836e907c31'}.items():assert sha(P/name)==digest,name
assert m['status']=='PREPARED_SOURCE_ONLY' and m['compiler_invocations']==0 and len(m['inputs'])==74
assert m['modules']==['GammaPsiBetaLimit22','GammaPsiIntegral22','GammaPsiDuplication22']
assert [x['declaration_count'] for x in m['catalog']]==[23,10,2] and m['declarations']==35
for row in m['inputs']:assert sha(Path(row['path']))==row['sha256'] and Path(row['path']).stat().st_size==row['bytes'],row['path']
for row in m['catalog']:assert sha(Path(row['path']))==row['sha256'] and len(row['declarations'])==row['declaration_count']
closure=read(Path(m['cache_closure_path']));assert closure['module_count']==len(closure['nodes'])==3238
assert closure['artifact_count']==len(closure['artifacts'])==6476
for row in closure['artifacts']:assert sha(Path(row['path']))==row['sha256'] and Path(row['path']).stat().st_size==row['bytes'],row['path']
assert sha(B/'round22/role3/h1_psi/revision03/psi_batch03_attempt01/GammaPsiCore22.olean')==m['readonly_psi_core_olean_sha256']=='15f66830eab0ee8e192d4fffee9518abd001b3167c28c527881bbdaabefb9a4b'
assert sha(B/'round22/judge5/batch02_attempt01/GammaPrerequisites22.olean')==m['readonly_gamma_olean_sha256']=='fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477'
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,digest in archives['sha256'].items():assert sha(B/rel)==digest,rel
assert not (P/'psi_batch04_attempt01').exists()
gate=read(C/'messages/round22_role3_psi_batch03_authorization1.json')
gate.update({'schema':'ROUND22_ROLE3_H1_PSI_BATCH04_AUTHORIZATION_V1','created_utc':datetime.now(timezone.utc).isoformat(),
 'stage':'H1_PSI_BATCH04','attempt':'psi_batch04_attempt01','modules':m['modules'],'compiler_invocations_maximum':3,
 'source_manifest_sha256':sha(mp),'launcher_sha256':sha(P/'run_psi_batch_once22.py'),'verified_inputs':74,
 'readonly_psi_core_olean_sha256':m['readonly_psi_core_olean_sha256'],
 'root_FULL_reads':{'Beta':'604408','Duplication':'37ce26','Integral_identical_prior':'0e6adc',
 'launcher':'f8f5b6','builder':'0ad0be','preparation_scope_diagnosis':'3b4814','prepared_final_reads':'1f08c5'},
 'manifest_scope':'Complete JSON parsed/all74 inputs and6476cachebytes hashed; no FULL raw cache/import mathematical claim',
 'previous_author_batches_closed':3,'Core_author_recompiled':False,'root_compiler_invocations':0,'root_numeric_invocations':0})
gp=C/'messages/round22_role3_psi_batch04_authorization1.json'
with gp.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json';cp=read(cpp);cp['phase']='ROUND22_PSI04_THREE_AUTHOR_CHILDREN_AUTHORIZED_GAMMA_DERIVATIVE_JUDGE_PASS_OBSERVATION_PENDING'
for a in cp['in_flight_executors']:
 if a['role']==3:a['status']='PSI04_THREE_AUTHOR_CHILDREN_AUTHORIZED_NOT_STARTED_CORE_READONLY'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'inputs_verified':74,'cache_artifacts_verified':6476,
 'archives_verified':3089,'root_compiler_invocations':0,'root_numeric_invocations':0,'WIN':False},indent=2))
