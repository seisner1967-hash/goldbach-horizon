"""Authorize exactly one frozen Lean author stage; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round22'; P=R/'role3'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'stage01_source_manifest.json'; launcher=P/'run_stage_once.py'
assert sha(mp)=='23b93f300ebba68e462f0e258048b4baca07bb7dea4804f656194d9f2b6ed443'
assert sha(launcher)=='25a364f023e00e0cad5d9e8308b1a46e8d1ae2a49fc75d892dd81b1e04bd06a0'
m=read(mp); assert len(m['inputs'])==19 and m['modules']==['EpsteinKernel22'] and m['actual_Lean_invocations']==0 and not m['victory']
for row in m['inputs']: assert sha(Path(row['path']))==row['sha256'],row['path']
assert sha(P/'EpsteinKernel22.lean')=='cd5cb975242aa38d7d118ac9378409c4bfe406d41227371a7006972d1c145053'
assert sha(P/'stage01_preparation.md')=='55feeb9e3b392d05ff920978c738b09019ddbc418054927854bfde263805be6f'
py=Path(r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'); lean=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
assert sha(py)=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(lean)=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
numeric=read(R/'role6/actual_epstein22/actual_receipt.json'); observed=read(C/'messages/round22_epstein_observation.json')
assert numeric['exit_code']==0 and numeric['post_integrity'] and observed['status']=='EPSTEIN_UNFOLDING_AUX_PASS' and observed['actual_attempts']==1
assert sha(R/'role6/actual_epstein22/epstein_result22.json')==numeric['result_sha256']==observed['hashes']['result']
assert not (P/'stage01_attempt01').exists()
gate={'schema':'round22.root.role3.compiler_authorization.v1','role':'ROLE3','actor_task':'/root/round22_formal3_prepare','node_id':'16.1','attempt':'stage01_attempt01','stage':'G0_KERNEL_STAGE01','authorized':True,'created_utc':datetime.now(timezone.utc).isoformat(),'numeric_verdict':'EPSTEIN_UNFOLDING_AUX_PASS','numeric_receipt_sha256':sha(R/'role6/actual_epstein22/actual_receipt.json'),'numeric_result_sha256':numeric['result_sha256'],'source_manifest_sha256':sha(mp),'launcher_sha256':sha(launcher),'python_sha256':sha(py),'lean_sha256':sha(lean),'modules':['EpsteinKernel22'],'no_win':True,'child_invocations_maximum':1,'hidden_retries_allowed':False,'unchanged_PASS_replay_allowed':False,'root_FULL_reads':{'source':'5633bf','launcher':'ba6811','preparation':'0ba86a','manifest_receipt':'19e5bb','phase_reads':'2dfcf3','metadata_builder':'09ba87','numeric':'115c5c+d0c146'},'formal_scope':'Real positive kernel, derived primitive/FTC, limits/integrability/full integral and deficit. Infinite periodized row and finite window not in this invocation.','forbidden_credits':['full_G0_unfolding','Weil','heat','operator_scattering','coefficient_N','D_N_bound','WIN'],'independent_judge_pending':True}
gp=C/'messages/round22_role3_stage01_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_AUX_PASS_ROLE3_FIRST_KERNEL_COMPILE_AUTHORIZED_NOT_STARTED'; cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_role3_stage01_authorization.json','round22/role3/stage01_source_manifest.json','round22/role3/stage01_preparation.md']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='ONE_KERNEL_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'status':'ROLE3_ONE_KERNEL_COMPILE_AUTHORIZED_NOT_STARTED','inputs_verified':19,'runtime_bytes_verified':2,'numeric_actual_PASS':True,'root_compiler_invocations':0,'win':False},ensure_ascii=False,indent=2))
