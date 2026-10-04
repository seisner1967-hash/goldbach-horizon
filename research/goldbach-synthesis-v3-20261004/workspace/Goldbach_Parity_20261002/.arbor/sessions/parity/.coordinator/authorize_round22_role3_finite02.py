"""Review-byte gate for one finite-window author compile; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role3/stage02'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'source_manifest.json'; launcher=P/'run_stage02_once.py'
assert sha(mp)=='2212fd2031c856a289328f1636615056d9c4fbaa0ad50d6aee4840b3bf4de1ae'
assert sha(launcher)=='3cf55b5486b1a87df8ba95622795bbde1337a62dd7a19e1e1467c6636307f2e9'
m=read(mp); assert m['modules']==['EpsteinFinite22'] and len(m['inputs'])==21
assert m['new_Lean_invocations']==0 and not m['Kernel_recompile'] and not m['victory']
for row in m['inputs']: assert sha(Path(row['path']))==row['sha256'],row['path']
assert sha(P/'EpsteinFinite22.lean')=='ed4d3bcf1c9427c157045356115445944f94224369458ba4bcceb91b17414434'
prepared=read(P/'prepared_receipt.json'); assert prepared['source_manifest_sha256']==sha(mp) and prepared['Lean_gate']=='CLOSED'
kernel=read(C/'messages/round22_kernel_pass02_observation.json')
assert kernel['exit_code']==0 and kernel['cumulative_round22_author_Lean_PASS']==1
dep=B/'round22/role3/revision02/stage01_attempt02/EpsteinKernel22.olean'
assert sha(dep)==m['dependency_olean_sha256']==kernel['olean_sha256']=='9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d'
gate=read(C/'messages/round22_role3_stage01_authorization.json')
for key,path in [('python_sha256',r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'),('lean_sha256',r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')]: assert sha(Path(path))==gate[key]
num=read(C/'messages/round22_epstein_observation.json'); assert num['status']=='EPSTEIN_UNFOLDING_AUX_PASS' and num['actual_attempts']==1
assert sha(B/'round22/role6/actual_epstein22/epstein_result22.json')==num['hashes']['result']==gate['numeric_result_sha256']
assert not (P/'stage02_attempt01').exists()
gate.update({'schema':'round22.root.role3.compiler_authorization.finite.v1','attempt':'stage02_attempt01','stage':'G0_FINITE_STAGE02','created_utc':datetime.now(timezone.utc).isoformat(),'modules':['EpsteinFinite22'],'source_manifest_sha256':sha(mp),'launcher_sha256':sha(launcher),'source_sha256':sha(P/'EpsteinFinite22.lean'),'dependency_olean_sha256':sha(dep),'Kernel_recompile':False,'root_FULL_reads':{'source':'6819d6','launcher':'437665','preparation':'2b4b32','metadata_builder':'de74e0','manifest':'d9caf3','read_receipts':'49fa36','prepared_receipt':'1aaaf1','kernel_actual':'861542+b39137+4cd2aa+db90a3'},'formal_scope':'Derived finite affine geometric window, signed substitution, negation isometry and endpoint telescope only; genuine infinite integral and continuous tail remain outside this child.'})
gp=C/'messages/round22_role3_stage02_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_KERNEL_AUTHOR_PASS_FINITE_STAGE02_ONE_COMPILE_AUTHORIZED'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_role3_stage02_authorization.json','round22/role3/stage02/source_manifest.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='FINITE_STAGE02_ONE_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':21,'actual_Kernel_olean_verified':True,'one_child':'EpsteinFinite22','Kernel_recompile':False,'root_compiler_invocations':0,'victory':False},ensure_ascii=False,indent=2))
