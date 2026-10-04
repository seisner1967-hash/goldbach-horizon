"""ROOT metadata authorization only: one new duplication source."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/role3/h1_psi/revision05'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'psi_source_manifest22.json';m=read(mp)
for name,digest in {'psi_source_manifest22.json':'6f47f2e2c6e8af0d2b0bf3decf0f8b04eee057cd9988f633fccf7682f2d1bb40',
 'run_psi_batch_once22.py':'78d41b24c5d680c3442bf9682bd49e1e822b734f1e7941d06c0c35da95c5d02c',
 'prepare_psi_metadata22.ps1':'9f740c22a922d2524b2749515296e93a1f7a5cff6a220ac906798b9b81a055ed',
 'psi_prepared_receipt22.json':'e5cdcc415bf4d8cdc8e0af76e30b459bc73bd8b5b7760099d07d5f0b34e46273',
 'final_read_receipt22.json':'edb8f59588fe08b5b24715bea971a685f0b278b36e6de12f322cf61fc1333434'}.items():assert sha(P/name)==digest,name
assert m['modules']==['GammaPsiDuplication22'] and m['status']=='PREPARED_SOURCE_ONLY' and m['compiler_invocations']==0
assert m['declarations']==2 and len(m['inputs'])==84 and m['catalog'][0]['sha256']=='0491177c6cfc1ef35b28796be404a3ca7975bac357cc6551b80d12333726812e'
for x in m['inputs']:assert sha(Path(x['path']))==x['sha256'] and Path(x['path']).stat().st_size==x['bytes'],x['path']
cl=read(Path(m['cache_closure_path']));assert cl['module_count']==3238 and len(cl['artifacts'])==6476
for x in cl['artifacts']:assert sha(Path(x['path']))==x['sha256'],x['path']
ar=read(B/'round22/previous_artifacts_sha256.json');assert ar['file_count']==3089
for rel,digest in ar['sha256'].items():assert sha(B/rel)==digest,rel
assert not (P/'psi_batch05_attempt01').exists()
g=read(C/'messages/round22_role3_psi_batch04_authorization1.json')
g.update({'schema':'ROUND22_ROLE3_H1_PSI_BATCH05_AUTHORIZATION_V1','created_utc':datetime.now(timezone.utc).isoformat(),
 'stage':'H1_PSI_BATCH05','attempt':'psi_batch05_attempt01','modules':m['modules'],'compiler_invocations_maximum':1,
 'source_manifest_sha256':sha(mp),'launcher_sha256':sha(P/'run_psi_batch_once22.py'),'verified_inputs':84,
 'root_FULL_reads':{'Dup_source_and_receipt':'50b076','launcher':'43e10d','builder':'36310c','preparation_finalread':'228858'},
 'manifest_scope':'Complete JSON parsed/all84 inputs and6476artifacts hashed; no FULL raw cache/API claim',
 'previous_author_batches_closed':4,'Core_Beta_Integral_author_recompiled':False,'root_compiler_invocations':0,'root_numeric_invocations':0})
gp=C/'messages/round22_role3_psi_batch05_authorization1.json'
with gp.open('x',encoding='utf-8') as f:json.dump(g,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json';cp=read(cpp)
for a in cp['in_flight_executors']:
 if a['role']==3:a['status']='PSI05_DUPLICATION_ONE_AUTHOR_CHILD_AUTHORIZED_NOT_STARTED'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'inputs_verified':84,'cache_artifacts_verified':6476,'archives_verified':3089,'root_compiler_invocations':0,'WIN':False},indent=2))
