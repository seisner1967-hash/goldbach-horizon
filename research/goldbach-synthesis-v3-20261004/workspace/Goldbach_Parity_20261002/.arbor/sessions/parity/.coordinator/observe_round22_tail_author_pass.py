"""Record author Tail PASS and conserved bytes; independent Judge still required."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
A=B/'round22/role3/stage04/stage04_attempt01'; P=A.parent
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); m=read(P/'source_manifest.json'); row=r['rows'][0]
assert sha(A/'receipt.json')=='d3c68016b792a02053e97901e7ab4759ff77652fa0835582124e86d9f7835c21'
assert r['status']=='AUTHOR_STAGE_AUX_PASS' and r['actual_child_invocations']==1 and row['exit_code']==0 and r['infinite_unfolding_complete'] and not r['victory']
assert sha(A/'EpsteinTail22.log')==row['log_sha256']=='af4334b90177fa791f1ee4cd1befd21c2039c70db2a08dbbd32b02663cce535d'
assert sha(A/'EpsteinTail22.olean')==row['olean_sha256']=='d6ca888b83bbd4644152da951df39b7712a2735ae10e233b84ea1dcb9584b025'
assert pre['inputs']==post['inputs']==m['inputs'] and len(pre['inputs'])==30 and post['unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==30
for p,e in zip(copies,pre['inputs']): assert sha(p)==e['sha256']==sha(Path(e['path'])),e['path']
assert sha(Path(pre['gate_path']))==pre['gate_sha256']
archives=read(B/'round22/previous_artifacts_sha256.json'); assert len(archives['sha256'])==3089
for path,digest in archives['sha256'].items(): assert sha(B/path)==digest,path
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'actual_author_compiler_children':1,'started':row['started_at'],'finished':row['finished_at'],'exit_code':0,'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'olean_sha256':row['olean_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':30,'inputs_verified':30,'archives_verified':3089,'root_FULL_reads':{'log_receipt':'71ee95'},'PRE_POST_scope':'Complete JSON parsed and all30 captures/current inputs checked; not whole text FULL displayed.','author_reported_standard_prints':14,'author_reported_theorems':11,'author_reported_definitions':3,'author_PASS':5,'author_FAIL':8,'official_modules':59,'official_auxiliary_declarations':993,'independent_Judge_Tail_credit':False,'finite_error_envelope_author_Lean_credit':True,'D_N_bound':False,'WIN':False,'root_compiler_invocations':0}
with (C/'messages/round22_tail_author_pass_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
insight='Tail actual author exit0,11theorems3definitions14standard axiom reports,30captures/current inputs and3089archives conserved. True infinite minus finite error, closed bound and joint continuity derived in author; independent Judge still pending. Full modular scattering/heat/coefficientN/D_N OPEN,noWin. Official59modules/993auxiliaries unchanged until independent audit.'
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — true continuous G0 tail author PASS\n\n'+insight+'\n','--score','0','--insight',insight,'--result','G0_UNFOLD_TAIL_AUTHOR_AUX_PASS_JUDGE_PENDING','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_tail_author_pass_observation.json')
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='G0_FOUR_MODULES_AUTHOR_PASS_JUDGE_PENDING_ACTOR_FINAL_REPORT'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nTail auteur : START08:35:09UTC, FIN08:35:31UTC, exit0, vraie erreur/enveloppe/continuité jointe dérivées ;11théorèmes+3définitions/14audits standards rapportés,30captures/inputs et3089archives vérifiés. Juge indépendant encore requis. Auteur22 :5PASS/8FAIL techniques. Officiel59modules/993auxiliaires conservé, aucune diffusion globale/coefficientN/D_N/WIN.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
