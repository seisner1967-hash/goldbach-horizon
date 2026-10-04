"""Authorize one reviewed correction; metadata only, no compiler or numeric call."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round22'; P=R/'role3/revision02'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'source_manifest.json'; launcher=P/'run_revision02_once.py'
assert sha(mp)=='8c16d9b471809ebfd093305d7f6e9e90284579cce3dcb95fc0dd9d3d5dd22265'
assert sha(launcher)=='ec1dc5ec8d9d80802d5a87b5573bd4f99ab0c91e3ad5a55236934d18e92fe51f'
m=read(mp)
assert len(m['inputs'])==30 and m['modules']==['EpsteinKernel22']
assert m['new_Lean_invocations']==0 and m['previous_actual_exit']==1 and not m['victory']
for row in m['inputs']: assert sha(Path(row['path']))==row['sha256'],row['path']
assert sha(P/'EpsteinKernel22.lean')=='b465bf53b124fa158eed1b5f01171d18ce7f8d7252bf27cf30db1ed7575a773c'
prepared=read(P/'prepared_receipt.json'); assert prepared['source_manifest_sha256']==sha(mp) and prepared['input_count']==30 and prepared['Lean_gate']=='CLOSED'
observed_fail=read(C/'messages/round22_kernel_failure01_observation.json')
assert observed_fail['actual_compiler_attempts']==1 and observed_fail['actual_Lean_FAIL']==1 and observed_fail['actual_Lean_PASS']==0
py=Path(r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
lean=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
assert sha(py)=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(lean)=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
numeric=read(R/'role6/actual_epstein22/actual_receipt.json'); observed=read(C/'messages/round22_epstein_observation.json')
assert numeric['exit_code']==0 and numeric['post_integrity'] and observed['status']=='EPSTEIN_UNFOLDING_AUX_PASS' and observed['actual_attempts']==1
assert sha(R/'role6/actual_epstein22/epstein_result22.json')==numeric['result_sha256']==observed['hashes']['result']
assert not (P/'stage01_attempt02').exists()
gate=read(C/'messages/round22_role3_stage01_authorization.json')
gate.update({'schema':'round22.root.role3.compiler_authorization.v2','attempt':'stage01_attempt02','stage':'G0_KERNEL_REVISION02','created_utc':datetime.now(timezone.utc).isoformat(),'source_manifest_sha256':sha(mp),'launcher_sha256':sha(launcher),'source_sha256':sha(P/'EpsteinKernel22.lean'),'previous_failure_observation_sha256':sha(C/'messages/round22_kernel_failure01_observation.json'),'root_FULL_reads':{'source':'1d6a2f','launcher':'bc45ec','preparation':'0069c4','manifest':'da6d04','metadata_builder':'32de0a','read_receipts':'579dc3','prepared_receipt':'1d56e2','actual_previous_failure':'9ed99b+32fa0b+668004','numeric':'115c5c+d0c146'},'correction_scope':'Separate frozen revision from actual technical compiler diagnostics; original and failure immutable.'})
gp=C/'messages/round22_role3_stage01_attempt02_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_AUX_PASS_ROLE3_KERNEL_REVISION02_COMPILE_AUTHORIZED_NOT_STARTED'
cp['previous_goal_turn_evidence'] += ['.arbor/sessions/parity/.coordinator/messages/round22_role3_stage01_attempt02_authorization.json','round22/role3/revision02/source_manifest.json','round22/role3/revision02/preparation.md']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='REVISION02_ONE_KERNEL_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'status':'ROLE3_REVISION02_ONE_KERNEL_COMPILE_AUTHORIZED_NOT_STARTED','inputs_verified':30,'runtime_bytes_verified':2,'numeric_unique_actual_PASS':True,'root_compiler_invocations':0,'win':False},ensure_ascii=False,indent=2))
