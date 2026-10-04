"""Authorize one reviewed constructive cast correction; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role3/stage02/revision03'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'source_manifest.json'; launcher=P/'run_revision03_once.py'
assert sha(mp)=='1ee8a02a9d56e9c5d9dfc65819a987c58cf05a5aea1a9a20c1f06a0a7dd08b70'
assert sha(launcher)=='9f3a51558e27a5ce6bbcec870651bae6f6309a14451437c7fd749389d29c4be6'
m=read(mp); assert len(m['inputs'])==43 and m['modules']==['EpsteinFinite22'] and m['previous_actual_exit']==1 and m['new_Lean_invocations']==0 and not m['victory']
for row in m['inputs']: assert sha(Path(row['path']))==row['sha256'],row['path']
assert sha(P/'EpsteinFinite22.lean')=='fb6205d1d88bbe864fd6c45f6ae60c5296812c966d9b2ce8bd2cccfc2128cc2d'
assert read(P/'prepared_receipt.json')['source_manifest_sha256']==sha(mp)
gate=read(C/'messages/round22_role3_stage02_attempt02_authorization.json')
for key,path in [('python_sha256',r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'),('lean_sha256',r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')]: assert sha(Path(path))==gate[key]
assert sha(B/'round22/role3/revision02/stage01_attempt02/EpsteinKernel22.olean')==m['dependency_olean_sha256']==gate['dependency_olean_sha256']
assert read(C/'messages/round22_finite_failure02_observation.json')['copies_verified']==32
assert sha(B/'round22/role6/actual_epstein22/epstein_result22.json')==gate['numeric_result_sha256']
assert not (P/'stage02_attempt03').exists()
gate.update({'schema':'round22.root.role3.compiler_authorization.finite.v3','attempt':'stage02_attempt03','stage':'G0_FINITE_REVISION03','created_utc':datetime.now(timezone.utc).isoformat(),'source_manifest_sha256':sha(mp),'launcher_sha256':sha(launcher),'source_sha256':sha(P/'EpsteinFinite22.lean'),'previous_failure_observation_sha256':sha(C/'messages/round22_finite_failure02_observation.json'),'previous_actual_attempt':'stage02_attempt02','root_FULL_reads':{'source':'80588c','launcher':'ee0fba','preparation':'1669f7','metadata_builder':'6daca0','manifest':'398e8e','read_receipts':'d57bc9','prepared_receipt':'d14a79','previous_actual_failure':'3997af+ca33f6+a65570'}})
gp=C/'messages/round22_role3_stage02_attempt03_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_ACTUAL_RUNNING_FINITE_REVISION03_ONE_COMPILE_AUTHORIZED'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_role3_stage02_attempt03_authorization.json','round22/role3/stage02/revision03/source_manifest.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='FINITE_REVISION03_ONE_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':43,'one_child':'EpsteinFinite22','Kernel_recompile':False,'root_compiler_invocations':0,'victory':False},ensure_ascii=False,indent=2))
