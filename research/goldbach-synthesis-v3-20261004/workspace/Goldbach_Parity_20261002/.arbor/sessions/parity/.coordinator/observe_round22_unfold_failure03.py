"""Observe third actual Unfold failure; status/byte metadata only."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round22/role3/stage03/revision03/stage03_attempt03'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); row=r['rows'][0]
assert r['actual_child_invocations']==1 and row['exit_code']==1 and row['olean_sha256'] is None and not r['victory']
assert sha(A/'EpsteinUnfold22.log')==row['log_sha256']=='d787a49762a25c8380211b856873ac93d5c3f90a4442070042edc498095a5f43'
assert pre['inputs']==post['inputs'] and len(pre['inputs'])==47 and post['unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==47
for p,e in zip(copies,pre['inputs']): assert sha(p)==e['sha256']==sha(Path(e['path']))
obs=read(C/'messages/round22_unfold_failure01_observation.json')
obs.update({'created_utc':datetime.now(timezone.utc).isoformat(),'stage':'G0_UNFOLD_REVISION03','started':row['started_at'],'finished':row['finished_at'],'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':47,'inputs_verified':47,'root_FULL_reads':{'log':'c8ca39','receipt':'7678c7'},'error_lines':[83],'error_count':1,'classes':['explicit rpow_natCast rewrite pattern absent; square normalization now resolved'],'cumulative_author_PASS':2,'cumulative_author_FAIL':7,'negSucc_cast_resolved':True})
with (C/'messages/round22_unfold_failure03_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
insight='Unfold third actual08:05:00..08:05:26UTC exit1,47captures conserved, one rpow_natCast pattern absent, square and negSucc resolved. Kernel/Finite PASS preserved; zero infinite G0 credit. Separate revision04SOURCE pending. AuthorRound22 2PASS7technicalFAIL; independentJudgeSOURCE,official57/942 unchanged,noWin.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — third infinite Unfold technical failure\n\n'+insight+'\n','--score','0','--insight',insight,'--result','KERNEL_FINITE_PASS_UNFOLD_THIRD_TECHNICAL_FAIL','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_UNFOLD_REVISION04_SOURCE_GAMMA_REVISION_SOURCE_JUDGE_PREPARING'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_unfold_failure03_observation.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='UNFOLD_THIRD_TECHNICAL_FAIL_REVISION04_SOURCE_ONLY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nUnfold22 troisième invocation réelle :08:05:00..08:05:26UTC exit1,47captures inchangées, un pattern rpow_natCast absent ; carré et negSucc corrigés. Zéro olean/infini complet, aucune réfutation analytique. Révision04 SOURCE séparée. Auteur22 :2PASS/7FAIL techniques.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
