"""ROOT byte checks and independent three-module gate only."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/judge5/batch04/three_modules'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'prepared_manifest.json';m=read(mp);cat=read(P/'catalog.json')
for name,digest in {'prepared_manifest.json':'162d544328c64989800156bc816095373eb19bb0308f1b49719e3f9491eadd05',
 'run_once.py':'2fdc406b57faed224314885218bd299bac6e1158dee8e43c7f0800e897473624',
 'prepare_metadata.py':'2ac0967a7bb0f29f9c6416c57be11531a63535693d2c525872adea4be20e6ea7',
 'prepared_receipt.json':'a6bbf2f5235421e0ba2bcbde828f9e12848959a5d9a68c406c397988d536cbd6',
 'catalog.json':'d58f7af4dfdeadabb228b85384bb08fd92e439be022f24fcac48328cdb2dc633',
 'read_receipts.json':'c54f83bd1abdf658c55d19bf3068554147b72740d7c45e72bd3c1465b04bd2aa'}.items():assert sha(P/name)==digest,name
assert m['status']=='PREPARED_SOURCE_ONLY_GATE_CLOSED' and m['unresolved_modules']==[]
assert m['modules']==['GammaPsiCore22','GammaPsiBetaLimit22','GammaPsiIntegral22'] and cat['total_declarations']==52
assert cat['theorem_count']==44 and cat['definition_count']==8
assert [x['source_sha256'] for x in cat['modules']]==['450962be9526866fa0ffebc39ef29a819d94b57a90000291337550e9f4dc7284','b4adf3ac71dd7c9d0e6e78f83ce805ddc7eaf5e8f5978aa4c1d6b87bc8caceb8','3f254cdfeee333aa66eba719b944f64a693fa2e15f0265f340ace9c2a99f6aaf']
assert len(m['immutable_inputs'])==6648 and m['import_module_count']==3238
for x in m['immutable_inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
old=read(P/'closed_judge_bindings.json');assert len(old['inputs'])==m['closed_judge_files']==134
for x in old['inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
ar=read(B/'round22/previous_artifacts_sha256.json');assert ar['file_count']==3089
for rel,digest in ar['sha256'].items():assert sha(B/rel)==digest,rel
assert not (P/'batch04_attempt01').exists()
g={'schema':'ROUND22_JUDGE5_BATCH04_AUTHORIZATION','role':'ROLE5','authorized':True,'attempt':'batch04_attempt01',
 'modules':m['modules'],'compiler_invocations_maximum':3,'source_manifest_sha256':sha(mp),'launcher_sha256':sha(P/'run_once.py'),
 'preparation_receipt_sha256':sha(P/'prepared_receipt.json'),'python_sha256':'4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c',
 'lean_sha256':'8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08','readonly_local_dependencies':[],
 'independent_audit':True,'author_olean_allowed':False,'no_win':True,'created_utc':datetime.now(timezone.utc).isoformat(),
 'root_FULL_reads':{'launcher':'755474','builder':'758b29','preparation':'f5c3ed','prepared_receipt':'620a74','read_receipts':'be9a35',
 'Core_identical_prior':'0e6adc','Beta_identical_prior':'604408','Integral_identical_prior':'0e6adc'},
 'manifest_scope':'Complete JSON parsed/all6648bytes and134closedJudgefiles/3089archives checked; no FULLraw cache mathclaim',
 'inputs_verified':6648,'archives_verified':3089,'root_compiler_invocations':0,'root_numeric_invocations':0}
gp=C/'messages/round22_judge5_batch04_authorization.json'
with gp.open('x',encoding='utf-8') as f:json.dump(g,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json';cp=read(cpp)
for a in cp['in_flight_executors']:
 if a['role']==5:a['status']='PSI52_THREE_NEW_INDEPENDENT_CHILDREN_AUTHORIZED_NOT_STARTED'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'inputs_verified':6648,'oldJudge_files_verified':134,'archives_verified':3089,'root_compiler_invocations':0,'WIN':False},indent=2))
