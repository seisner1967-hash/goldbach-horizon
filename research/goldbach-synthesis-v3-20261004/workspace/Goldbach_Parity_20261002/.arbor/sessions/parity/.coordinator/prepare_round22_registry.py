"""Bind immutable archives for continuous22, only byte hashes and metadata."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round22'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
previous=read(B/'round21/previous_artifacts_sha256.json')['sha256']
assert len(previous)==3028
controller=B/'round21/controller_interrupted_manifest.json'; interrupted=read(controller)
assert interrupted['status']=='INTERRUPTED_BY_EXPLICIT_USER_PIVOT_NOT_MATHEMATICAL_FAILURE'
bindings={**previous,**interrupted['bindings'],str(controller.relative_to(B)).replace('\\','/'):sha(controller)}
assert len(bindings)==3089
for path,digest in bindings.items(): assert sha(B/path)==digest,path
registry={'status':'ROUND22_CONTINUOUS_PIVOT_PROTECTED_ARCHIVES','created_utc':datetime.now(timezone.utc).isoformat(),'file_count':len(bindings),'previous3028':3028,'interrupted21_files_with_controller61':61,'controller21_sha256':sha(controller),'sha256':bindings,'numerical_or_Lean_execution_by_root':False,'preflight_by_numeric_role_pending':True}
target=R/'previous_artifacts_sha256.json'; assert not target.exists(); target.write_text(json.dumps(registry,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json'); cp.update(current_protected_artifacts=3089,current_protected_registry='round22/previous_artifacts_sha256.json',current_protected_registry_sha256=sha(target),next_protected_artifacts_expected=3089)
cp['in_flight_executors']=[{'role':1,'agent':'/root/round21_formal3_prepare','ownership':['round22/role1/**','round22/agent1_continuous.md'],'status':'SPECTRAL_AND_MODULAR_IDEATION_ONLY'},{'role':2,'agent':'/root/round21_ideation1_signed','ownership':['round22/role2/**','round22/agent2_operator.md'],'status':'OPERATOR_ADELIC_IDEATION_ONLY'},{'role':6,'agent':'/root/round21_numeric_conservation','ownership':['round22/role6/**','round22/agent6_precontract.md'],'status':'CONTINUOUS_TRUNCATION_PRECONTRACT_READ_RESEARCH_ONLY_NO_PRODUCER'}]
cp['previous_goal_turn_evidence']+=['round22/previous_artifacts_sha256.json']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
observation={'status':'ROUND22_REGISTRY_ACTUAL_3089_BYTE_BINDINGS_VERIFIED','created_utc':datetime.now(timezone.utc).isoformat(),'protected_files':3089,'registry_sha256':sha(target),'new_mathematical_or_Lean_invocations':0,'all_math_Lean_gates_closed':True,'victory':False}
(C/'messages/round22_registry_preparation.json').write_text(json.dumps(observation,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(observation,ensure_ascii=False,indent=2))
