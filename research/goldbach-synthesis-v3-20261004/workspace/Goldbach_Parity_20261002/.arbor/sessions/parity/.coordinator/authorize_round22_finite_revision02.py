"""Gate a separate correction of Finite; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role3/stage02/revision02'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'source_manifest.json'; launcher=P/'run_revision02_once.py'
assert sha(mp)=='01d4513ac7fa8452c82ea1528ec04e0848487e8f7918749cfedd1b8fab4b988f'
assert sha(launcher)=='8a8020d5baae410b847cf09a10c2e200e66d17902bf0dab93165a14c5427ecb8'
m=read(mp); assert m['modules']==['EpsteinFinite22'] and len(m['inputs'])==32 and m['previous_actual_exit']==1
assert m['new_Lean_invocations']==0 and not m['victory']
for row in m['inputs']: assert sha(Path(row['path']))==row['sha256'],row['path']
assert sha(P/'EpsteinFinite22.lean')=='3510835ffa17206cdbb0bc9da76d1a13bfd304d8229164a658677831ef1c6076'
prepared=read(P/'prepared_receipt.json'); assert prepared['source_manifest_sha256']==sha(mp) and prepared['Lean_gate']=='CLOSED'
gate=read(C/'messages/round22_role3_stage02_authorization.json')
for key,path in [('python_sha256',r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'),('lean_sha256',r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')]: assert sha(Path(path))==gate[key]
assert sha(B/'round22/role3/revision02/stage01_attempt02/EpsteinKernel22.olean')==m['dependency_olean_sha256']==gate['dependency_olean_sha256']
failure=read(C/'messages/round22_finite_failure01_observation.json'); assert failure['exit_code']==1 and failure['copies_verified']==21
num=read(C/'messages/round22_epstein_observation.json'); assert num['status']=='EPSTEIN_UNFOLDING_AUX_PASS' and num['actual_attempts']==1
assert sha(B/'round22/role6/actual_epstein22/epstein_result22.json')==num['hashes']['result']==gate['numeric_result_sha256']
assert not (P/'stage02_attempt02').exists()
gate.update({'schema':'round22.root.role3.compiler_authorization.finite.v2','attempt':'stage02_attempt02','stage':'G0_FINITE_REVISION02','created_utc':datetime.now(timezone.utc).isoformat(),'source_manifest_sha256':sha(mp),'launcher_sha256':sha(launcher),'source_sha256':sha(P/'EpsteinFinite22.lean'),'previous_failure_observation_sha256':sha(C/'messages/round22_finite_failure01_observation.json'),'root_FULL_reads':{'source':'e4d64c','launcher':'fb48cd','preparation':'b2c552','metadata_builder':'7bf4f1','manifest':'15df81','read_receipts':'c38aa0','prepared_receipt':'516c0c','previous_actual_fail':'2d46e7+1b4568+9cf591'},'previous_actual_attempt':'stage02_attempt01','previous_actual_exit':1})
gp=C/'messages/round22_role3_stage02_attempt02_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_NUMERIC_AUTHORIZED_FINITE_REVISION02_ONE_COMPILE_AUTHORIZED'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_role3_stage02_attempt02_authorization.json','round22/role3/stage02/revision02/source_manifest.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='FINITE_REVISION02_ONE_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':32,'one_child':'EpsteinFinite22','Kernel_recompile':False,'root_compiler_invocations':0,'victory':False},ensure_ascii=False,indent=2))
