"""Observe actual compiler failure and independent numeric START; metadata only."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round22/role3/stage02/revision02/stage02_attempt02'; G=B/'round22/role6/gamma_h2/actual_gamma22'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
    with p.open('x',encoding='utf-8') as f: json.dump(v,f,ensure_ascii=False,indent=2); f.write('\n')
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); row=r['rows'][0]
assert r['actual_child_invocations']==1 and row['exit_code']==1 and row['olean_sha256'] is None and not r['victory']
assert sha(A/'EpsteinFinite22.log')==row['log_sha256']=='87786212873900e217c2604efdc8f20d69fc2dba3e213a62eb767490256f3463'
assert pre['inputs']==post['inputs'] and len(pre['inputs'])==32 and post['unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==32
for p,e in zip(copies,pre['inputs']): assert sha(p)==e['sha256']==sha(Path(e['path']))
obs=read(C/'messages/round22_finite_failure01_observation.json')
obs.update({'created_utc':datetime.now(timezone.utc).isoformat(),'cumulative_author_Lean_FAIL':3,'stage':'G0_FINITE_REVISION02','started':row['started_at'],'finished':row['finished_at'],'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'receipt_sha256':sha(A/'receipt.json'),'PREEXEC_sha256':sha(A/'PREEXEC.json'),'POSTEXEC_sha256':sha(A/'POSTEXEC.json'),'copies_verified':32,'FULL_root_log':'3997af','FULL_root_receipt':'ca33f6','FULL_root_START':'a65570','error_classes':['Int.negSucc/natAbs simplification creates absolute-value target instead of constructive successor cast'],'next':'Separate revision03 source and distinct gate, no automatic retry.'})
save(C/'messages/round22_finite_failure02_observation.json',obs)
start=read(G/'actual_START.json'); captures=read(G/'PREEXEC_captures.json'); assert start['captures_complete'] and len(captures['captures'])==17 and not captures['math_started']
for e in captures['captures']: assert sha(Path(e['copy']))==e['sha256']==sha(Path(e['source']))
assert start['attempt_token']==captures['attempt_token']=='bd36b071eadf487fa05981855dd4ea0a'
assert sha(Path(start['gate_path']))==start['gate_sha256']=='a1c30ab747bd3395fecb8dd4a250c0146338dfc0dad3f85c2174f9743b9b8835'
gobs={'scope':'ACTUAL_GAMMA_START_AND_PREEXEC_BYTE_OBSERVATION_ONLY_NO_VERDICT','observed_utc':datetime.now(timezone.utc).isoformat(),'actual_START':start['time_utc'],'token':start['attempt_token'],'root_FULL_START':'575485','root_FULL_captures':'ce0775','copies_verified':17,'actual_started_math_attempts':1,'result_claim':None,'root_math_invocations':0,'WIN':False,'period_note_FULL':'d6c16d','period_note_sha256':sha(G.parent/'gamma_period_width_note22.md'),'period_note_scope':'Generic period-width count2^18 versus paper2^16; implemented2^48 guard and outward enclosures unchanged; documentary note outside frozen producer bindings.'}
save(C/'messages/round22_gamma_actual_START_observation.json',gobs)
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
insight='Kernel authorPASS preserved; Finite second actual attempt07:29:48..07:30:11UTC exit1, only Int.negSucc/natAbs normalization remains,32capturedinputs unchanged,noolean. AuthorRound22 1PASS3FAIL, no parity/analytic refutation. Separate revision03SOURCE pending. Gamma unique new mathematical attempt started07:28:40UTC,17captures verified,no verdict credited; noWin/globalD_N.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — second finite technical failure\n\n'+insight+'\n','--score','0','--insight',insight,'--result','KERNEL_AUTHOR_PASS_FINITE_SECOND_TECHNICAL_FAIL_SOURCE_REVISION03_PENDING','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_ACTUAL_RUNNING_FINITE_SECOND_FAIL_SOURCE_REVISION03'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_finite_failure02_observation.json','.arbor/sessions/parity/.coordinator/messages/round22_gamma_actual_START_observation.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='FINITE_SECOND_TECHNICAL_FAIL_SOURCE_REVISION03_ONLY'
    if actor['role']==6: actor['status']='GAMMA_UNIQUE_ACTUAL_MATH_RUNNING_NO_VERDICT'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nFenêtre finie22, deuxième invocation réelle : exit1 à07:30:11UTC, une erreur de normalisation Int.negSucc/natAbs restante ;32captures inchangées, zéroolean. Noyau auteurPASS intact ; aucune réfutation analytique. BancΓ distinct réellement démarré à07:28:40UTC,17captures, sans verdict anticipé ni paiementD_N.\n')
print(json.dumps({'finite_failure':obs,'Gamma_start':gobs},ensure_ascii=False,indent=2))
