"""Observe second actual Unfold failure; status/byte metadata only."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round22/role3/stage03/revision02/stage03_attempt02'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); row=r['rows'][0]
assert r['actual_child_invocations']==1 and row['exit_code']==1 and row['olean_sha256'] is None and not r['victory']
assert sha(A/'EpsteinUnfold22.log')==row['log_sha256']=='cada439643be37f61f15393e9c0bb88e1cfd1dc8784a267921f8d62e95ec4ab7'
assert pre['inputs']==post['inputs'] and len(pre['inputs'])==36 and post['unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==36
for p,e in zip(copies,pre['inputs']): assert sha(p)==e['sha256']==sha(Path(e['path']))
obs=read(C/'messages/round22_unfold_failure01_observation.json')
obs.update({'created_utc':datetime.now(timezone.utc).isoformat(),'stage':'G0_UNFOLD_REVISION02','started':row['started_at'],'finished':row['finished_at'],'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':36,'inputs_verified':36,'root_FULL_reads':{'log':'f698a6','receipt':'94bbe8'},'error_lines':[60,173],'error_count':2,'classes':['real rpow versus natural pow coercion remains','simp made no progress in square normalization'],'cumulative_author_PASS':2,'cumulative_author_FAIL':6,'negSucc_cast_resolved':True})
with (C/'messages/round22_unfold_failure02_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
insight='Unfold second actual07:57:27..07:57:53UTC exit1,36captures conserved, two rpow/pow and simp-no-progress errors,negSucc resolved. Kernel/Finite PASS preserved; zero infinite G0 credit. Separate revision03SOURCE pending. AuthorRound22 2PASS6technicalFAIL; independentJudgeSOURCE,official57/942 unchanged,noWin.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — second infinite Unfold technical failure\n\n'+insight+'\n','--score','0','--insight',insight,'--result','KERNEL_FINITE_PASS_UNFOLD_SECOND_TECHNICAL_FAIL','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_UNFOLD_REVISION03_SOURCE_GAMMA_REVISION_SOURCE_JUDGE_PREPARING'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_unfold_failure02_observation.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='UNFOLD_SECOND_TECHNICAL_FAIL_REVISION03_SOURCE_ONLY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nUnfold22 deuxième invocation réelle :07:57:27..07:57:53UTC exit1,36captures inchangées, deux normalisations rpow/pow et simp restantes ; negSucc corrigé. Zéro olean/infini complet, aucune réfutation analytique. Révision03 SOURCE séparée. Auteur22 :2PASS/6FAIL techniques.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
