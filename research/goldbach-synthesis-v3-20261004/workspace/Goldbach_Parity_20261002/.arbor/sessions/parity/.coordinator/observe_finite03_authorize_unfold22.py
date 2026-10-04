"""Observe actual Finite PASS and authorize one Unfold child; metadata only."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round22/role3/stage02/revision03/stage02_attempt03'; P=B/'round22/role3/stage03'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
    with p.open('x',encoding='utf-8') as f: json.dump(v,f,ensure_ascii=False,indent=2); f.write('\n')
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); row=r['rows'][0]
assert r['status']=='AUTHOR_STAGE_AUX_PASS' and r['actual_child_invocations']==1 and row['exit_code']==0 and not r['victory']
assert sha(A/'EpsteinFinite22.log')==row['log_sha256']=='2fba74bbb307e13e60221866ac0648a97dcffca1003c73cf15e59a3b8c89acca'
assert sha(A/'EpsteinFinite22.olean')==row['olean_sha256']=='679f572be0d81f8c86bfa418fb460d5168774fc56b2b2537a9469ff0aca7a544'
assert len(pre['inputs'])==43 and pre['inputs']==post['inputs'] and post['unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==43
for p,e in zip(copies,pre['inputs']): assert sha(p)==e['sha256']==sha(Path(e['path']))
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'actual_child_invocations':1,'started':row['started_at'],'finished':row['finished_at'],'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'olean_sha256':row['olean_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':43,'inputs_verified':43,'root_FULL_reads':{'log':'8912ac','receipt':'8fd160','START':'fb3b09'},'round22_author_PASS':2,'round22_author_FAIL':3,'independent_judge_pending':True,'official_modules':57,'official_auxiliary_statements':942,'root_math_invocations':0,'D_N_claim':False,'WIN':False}
save(C/'messages/round22_finite_pass03_observation.json',obs)
mp=P/'source_manifest.json'; m=read(mp)
assert sha(mp)=='6af00ef3e03420b8c145da5a6ed8f91e66c1023d8f6e8d7a7a192fbb379fb312'
assert len(m['inputs'])==25 and m['modules']==['EpsteinUnfold22'] and m['new_Lean_invocations']==0 and not m['victory']
for e in m['inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert sha(P/'EpsteinUnfold22.lean')=='10323e3bd95202e9a00b222f5d2fcc4df9f15d769cb00cfc1e64344ce74a5875'
assert sha(P/'run_stage03_once.py')=='775c90f7f1555691c96c9d33a4c7488b4cd2a5173c8619426ceda7577215e563'
assert read(P/'prepared_receipt.json')['source_manifest_sha256']==sha(mp)
gate=read(C/'messages/round22_role3_stage02_attempt03_authorization.json')
for key,path in [('python_sha256',r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'),('lean_sha256',r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')]: assert sha(Path(path))==gate[key]
assert sha(B/'round22/role3/revision02/stage01_attempt02/EpsteinKernel22.olean')=='9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d'
assert m['dependency_olean_sha256']==row['olean_sha256']
assert sha(B/'round22/role6/actual_epstein22/epstein_result22.json')==gate['numeric_result_sha256']
assert not (P/'stage03_attempt01').exists()
gate.update({'schema':'round22.root.role3.compiler_authorization.unfold.v1','attempt':'stage03_attempt01','stage':'G0_UNFOLD_STAGE03','modules':['EpsteinUnfold22'],'created_utc':datetime.now(timezone.utc).isoformat(),'source_manifest_sha256':sha(mp),'launcher_sha256':sha(P/'run_stage03_once.py'),'source_sha256':sha(P/'EpsteinUnfold22.lean'),'dependency_olean_sha256':row['olean_sha256'],'dependency_pass_observation_sha256':sha(C/'messages/round22_finite_pass03_observation.json'),'root_FULL_reads':{'source':'47a01f','launcher':'532e1e','preparation':'2d65f6','metadata_builder':'bc6d12','manifest':'24c412','read_receipts':'3d4ae7','prepared_receipt':'42a6ac'},'Kernel_recompile':False,'Finite_recompile':False})
for key in ['previous_failure_observation_sha256','previous_actual_attempt']: gate.pop(key,None)
gp=C/'messages/round22_role3_stage03_authorization.json'; save(gp,gate)
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
insight='Finite revision03 actual07:35:44..07:36:07UTC exit0,43 captures/inputs unchanged,18 standard axiom prints. Kernel and Finite author PASS; cumulative author2PASS3technicalFAIL before Gamma result. Infinite Unfold final sourceFULL and25bindings checked; one distinct child authorized, no dependency recompile. Judge pending, official57/942 preserved; global trace/coefficientN/D_N OPEN,noWin.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — finite author PASS, infinite Unfold authorized\n\n'+insight+'\n','--score','0','--insight',insight,'--result','KERNEL_FINITE_AUTHOR_PASS_UNFOLD_ONE_CHILD_AUTHORIZED_GLOBAL_OPEN','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_AUTHOR_COMPILE_PENDING_UNFOLD_ONE_CHILD_AUTHORIZED'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_finite_pass03_observation.json','.arbor/sessions/parity/.coordinator/messages/round22_role3_stage03_authorization.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='KERNEL_FINITE_AUTHOR_PASS_UNFOLD_ONE_CHILD_AUTHORIZED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nFinite22 revision03 : invocation réelle07:35:44..07:36:07UTC exit0,43 captures inchangées,18 audits standards. Unfold infini final est lu FULL avec25bindings vérifiés ; une compilation distincte est autorisée, sans recompilation Kernel/Finite. Juge indépendant et trace globale restent ouverts ; aucun WIN.\n')
print(json.dumps({'finite_observation':obs,'unfold_gate':str(gp),'gate_sha256':sha(gp),'Unfold_verified_inputs':25,'root_compiler_invocations':0},ensure_ascii=False,indent=2))
