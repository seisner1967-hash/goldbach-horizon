"""Observe author output and captured bytes; no compilation or independent audit."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round22/role3/revision02/stage01_attempt02'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json')
assert r['actual_child_invocations']==1 and r['status']=='AUTHOR_STAGE_AUX_PASS' and not r['victory']
row=r['rows'][0]; assert row['exit_code']==0 and r['all_source_inputs_unchanged'] and post['unchanged']
assert pre['inputs']==post['inputs'] and len(pre['inputs'])==30
assert row['log_sha256']==sha(A/'EpsteinKernel22.log')=='70182795d884a636bf5c89904a21ee83f4ce9c83fea2c718093a60cb2a275886'
assert row['olean_sha256']==sha(A/'EpsteinKernel22.olean')=='9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d'
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==30
for p,input_row in zip(copies,pre['inputs']):
    assert sha(p)==input_row['sha256'] and sha(Path(input_row['path']))==input_row['sha256']
assert pre['gate_sha256']==sha(Path(pre['gate_path']))=='425cf29b0eb6f0dee64d579b5ff8241973aa4ae5efc79d2c8b8e6fdfc8e0d898'
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'scope':'AUTHOR_COMPILER_OUTPUT_AND_BYTE_CAPTURE_OBSERVATION_ONLY_INDEPENDENT_JUDGE_PENDING','actor':'ROLE3','actual_new_child_invocations':1,'cumulative_round22_author_Lean_PASS':1,'cumulative_round22_author_Lean_FAIL':1,'started':row['started_at'],'finished':row['finished_at'],'exit_code':0,'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'olean_sha256':row['olean_sha256'],'receipt_sha256':sha(A/'receipt.json'),'PREEXEC_sha256':sha(A/'PREEXEC.json'),'POSTEXEC_sha256':sha(A/'POSTEXEC.json'),'FULL_root_log':'861542','FULL_root_receipt':'b39137','FULL_root_START':'4cd2aa','FULL_root_PRE_POST':'db90a3','copies_verified':30,'numeric_unique_G0_AUX_PASS_preserved':True,'author_declared_axiom_outputs':33,'source_theorems':28,'source_definitions':5,'independent_judge':False,'official_modules':57,'official_auxiliary_theorems':942,'root_compiler_invocations':0,'infinite_G0_complete':False,'D_N_bound':False,'victory':False,'next':'Finite-window and genuine infinite unfolding sources plus derived continuous tail, separate compile gates; fresh independent Judge later.'}
target=C/'messages/round22_kernel_pass02_observation.json'
with target.open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
insight='Unique actual G0 numeric24case AUX_PASS preserved. Kernel revision02 real author compile07:14:47..07:15:17UTC exit0,30PREcopies unchanged, log and olean bound. Previous technicalFAIL preserved. Author PASS auxiliary only, fresh independentJudge pending, official57/942 unchanged. Infinite unfolding/continuous tail and global coefficientN/D_N OPEN; noWin.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — first author kernel PASS\n\n'+insight+'\n','--score','0','--insight',insight,'--result','ACTUAL_G0_NUMERIC_AUX_PASS_KERNEL_AUTHOR_AUX_PASS_INDEPENDENT_JUDGE_PENDING','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_AUX_PASS_KERNEL_AUTHOR_PASS_FINITE_UNFOLDING_TAIL_SOURCE_PREPARATION'
cp['previous_goal_turn_evidence']+=['round22/role3/revision02/stage01_attempt02/receipt.json','round22/role3/revision02/stage01_attempt02/EpsteinKernel22.log','.arbor/sessions/parity/.coordinator/messages/round22_kernel_pass02_observation.json','.arbor/sessions/parity/.coordinator/messages/round22_gamma_prepared2_observation.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='KERNEL_AUTHOR_AUX_PASS_FINITE_UNFOLDING_TAIL_SOURCE_ONLY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
report=B/'REPORT.md'; body=report.read_text(encoding='utf-8')
needle="Une correction en sources est en cours. Aucun module22 n'a encore compilé avec succès ou été certifié par le Juge."
assert body.count(needle)==1
body=body.replace(needle,"La révision02 du noyau a réellement compilé à07:15:17UTC avec exit0, 28théorèmes et5définitions ; 33sorties axioms standard sont dans le log. C'est un PASS d'auteur auxiliaire, avec contrôle indépendant encore attendu. Le déroulement infini et la queue continue restent en sources, et le bilan globalD_N reste ouvert.")
report.write_text(body,encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
