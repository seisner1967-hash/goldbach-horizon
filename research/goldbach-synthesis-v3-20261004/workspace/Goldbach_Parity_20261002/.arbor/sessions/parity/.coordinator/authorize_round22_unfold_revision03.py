"""Authorize one reviewed Unfold revision after the genuine failure; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role3/stage03/revision03'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'source_manifest.json'; launcher=P/'run_revision03_once.py'; m=read(mp)
assert sha(mp)=='56a45886e972c2137048b43df094822a72097dfdc839b044bdf3d6c7f8c6e405'
assert sha(launcher)=='b610d1132062a4d96014847c497058b17a9538e10171ebaf7566f797a4122683'
assert len(m['inputs'])==47 and m['modules']==['EpsteinUnfold22'] and m['previous_actual_exit']==1 and m['new_Lean_invocations']==0 and not m['victory']
for e in m['inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert sha(P/'EpsteinUnfold22.lean')=='930f6d68ea6ab6549e4e1e08fe701239685948e38b77b8c56487401c20da2935'
assert read(P/'prepared_receipt.json')['source_manifest_sha256']==sha(mp)
gate=read(C/'messages/round22_role3_stage03_attempt02_authorization.json')
for key,path in [('python_sha256',r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'),('lean_sha256',r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')]: assert sha(Path(path))==gate[key]
assert sha(B/'round22/role3/stage02/revision03/stage02_attempt03/EpsteinFinite22.olean')==m['dependency_olean_sha256']==gate['dependency_olean_sha256']
assert sha(B/'round22/role3/revision02/stage01_attempt02/EpsteinKernel22.olean')=='9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d'
failure=C/'messages/round22_unfold_failure02_observation.json'; assert read(failure)['copies_verified']==36
assert sha(B/'round22/role6/actual_epstein22/epstein_result22.json')==gate['numeric_result_sha256']
assert not (P/'stage03_attempt03').exists()
gate.update({'schema':'round22.root.role3.compiler_authorization.unfold.v3','attempt':'stage03_attempt03','stage':'G0_UNFOLD_REVISION03','created_utc':datetime.now(timezone.utc).isoformat(),'source_manifest_sha256':sha(mp),'launcher_sha256':sha(launcher),'source_sha256':sha(P/'EpsteinUnfold22.lean'),'previous_failure_observation_sha256':sha(failure),'previous_actual_attempt':'stage03_attempt02','root_FULL_reads':{'source':'9bf20f','launcher':'4694e3','preparation':'85629a','metadata_builder':'34b3e5','manifest':'345070','read_receipts':'8af208','prepared_receipt':'269371','previous_actual_failure':'f698a6+94bbe8'}})
gp=C/'messages/round22_role3_stage03_attempt03_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_UNFOLD_REVISION03_ONE_CHILD_AUTHORIZED_GAMMA_REVISION_SOURCE'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_role3_stage03_attempt03_authorization.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='UNFOLD_REVISION03_ONE_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':47,'one_child':'EpsteinUnfold22','root_compiler_invocations':0,'WIN':False},ensure_ascii=False,indent=2))
