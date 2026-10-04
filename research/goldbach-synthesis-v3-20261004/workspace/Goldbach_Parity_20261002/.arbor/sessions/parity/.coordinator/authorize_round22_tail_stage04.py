"""Authorize one Tail child after final SOURCE review; coordinator metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role3/stage04'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'source_manifest.json'; m=read(mp); launcher=P/'run_stage04_once.py'
assert sha(mp)=='ab0c0442f7c9bbe84e1880b242166e6d3dcfb4cea801c70139d9c262fa13d12b'
assert sha(launcher)=='431e60bb7f61c6b73dc8917bd0f5346f7965876daaccfef7e8433131c15aec07'
assert sha(P/'EpsteinTail22.lean')=='5f9d3f180df2e165d43aebfe2e72b963091bb2b90fdfa4e786a66cc82745af8e'
assert len(m['inputs'])==30 and m['modules']==['EpsteinTail22'] and m['new_Lean_invocations']==0 and not m['victory']
for e in m['inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert read(P/'prepared_receipt.json')['source_manifest_sha256']==sha(mp)
gate=read(C/'messages/round22_role3_stage03_attempt04_authorization.json')
assert sha(B/'round22/role3/stage03/revision04/stage03_attempt04/EpsteinUnfold22.olean')==m['dependency_olean_sha256']=='b3e0d60e7633cc46e2084c0131e2fd42aef0f1fca60d4db7682d45ece1774bc0'
ob=read(C/'messages/round22_unfold_author_pass_observation.json'); assert ob['exit_code']==0 and ob['copies_verified']==58
assert sha(B/'round22/role6/actual_epstein22/epstein_result22.json')==gate['numeric_result_sha256']
assert not (P/'stage04_attempt01').exists()
gate.update({'schema':'round22.root.role3.compiler_authorization.tail.v1','attempt':'stage04_attempt01','stage':'G0_TAIL_STAGE04','created_utc':datetime.now(timezone.utc).isoformat(),'modules':['EpsteinTail22'],'source_manifest_sha256':sha(mp),'launcher_sha256':sha(launcher),'source_sha256':sha(P/'EpsteinTail22.lean'),'dependency_olean_sha256':m['dependency_olean_sha256'],'previous_actual_attempt':'stage03_attempt04_AUTHOR_PASS','root_FULL_reads':{'source_and_launcher':'b2b8ef','preparation_builder_reads_prepared':'e6ee74'},'root_manifest_scope':'Complete manifest parsed and all30 immutable bytes checked; whole text read in current task.','numeric_replay':False,'no_win':True})
gp=C/'messages/round22_role3_stage04_authorization.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_TAIL_ONE_AUTHOR_CHILD_AUTHORIZED_GAMMA3_ACTUAL_JUDGE_PENDING'
cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_role3_stage04_authorization.json')
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='TAIL_STAGE04_ONE_CHILD_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':30,'one_child':'EpsteinTail22','root_compiler_invocations':0,'WIN':False},ensure_ascii=False,indent=2))
