"""Record author Unfold PASS and conserved bytes; independent Judge still required."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
A=B/'round22/role3/stage03/revision04/stage03_attempt04'; P=A.parent
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); m=read(P/'source_manifest.json'); row=r['rows'][0]
assert sha(A/'receipt.json')=='4a6677cebe40f404ebc366d35227e31584f6b0d53962b1d61d84d5c3703ffb08'
assert r['status']=='AUTHOR_STAGE_AUX_PASS' and r['actual_child_invocations']==1 and row['exit_code']==0 and r['infinite_unfolding_complete'] and not r['victory']
assert sha(A/'EpsteinUnfold22.log')==row['log_sha256']=='12cc50cc686994a04af46290727ed38de7e11eaf09622c67d5fcfb1544c63060'
assert sha(A/'EpsteinUnfold22.olean')==row['olean_sha256']=='b3e0d60e7633cc46e2084c0131e2fd42aef0f1fca60d4db7682d45ece1774bc0'
assert pre['inputs']==post['inputs']==m['inputs'] and len(pre['inputs'])==58 and post['unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==58
for p,e in zip(copies,pre['inputs']): assert sha(p)==e['sha256']==sha(Path(e['path'])),e['path']
assert sha(Path(pre['gate_path']))==pre['gate_sha256']
archives=read(B/'round22/previous_artifacts_sha256.json'); assert len(archives['sha256'])==3089
for path,digest in archives['sha256'].items(): assert sha(B/path)==digest,path
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'actual_author_compiler_children':1,'started':row['started_at'],'finished':row['finished_at'],'exit_code':0,'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'olean_sha256':row['olean_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':58,'inputs_verified':58,'archives_verified':3089,'root_FULL_reads':{'log_receipt_START':'976498'},'PRE_POST_scope':'Complete JSON parsed and all58 captures/current inputs checked; not whole text FULL displayed.','author_reported_standard_prints':19,'author_reported_theorems':16,'author_reported_definitions':3,'author_PASS':3,'author_FAIL':8,'official_modules':59,'official_auxiliary_declarations':993,'independent_Judge_Unfold_credit':False,'finite_error_envelope_Lean_credit':False,'D_N_bound':False,'WIN':False,'root_compiler_invocations':0}
with (C/'messages/round22_unfold_author_pass_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
insight='Unfold revision04 actual author exit0,16theorems3definitions19standard axiom reports,58captures/current inputs and3089archives conserved. True infinite geometric G0 derived, independent Judge still pending. Tail envelope SOURCE preparation only; full modular scattering/heat/coefficientN/D_N OPEN,noWin. Official59modules/993auxiliaries unchanged until independent audit.'
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — true infinite G0 author PASS\n\n'+insight+'\n','--score','0','--insight',insight,'--result','UNFOLD_AUTHOR_AUX_PASS_TAIL_SOURCE_JUDGE_PENDING','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_unfold_author_pass_observation.json')
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='UNFOLD_ACTUAL_AUTHOR_PASS_TAIL_SOURCE_PREPARATION_JUDGE_PENDING'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nUnfold04 auteur : START08:29:04UTC, FIN08:29:29UTC, exit0, vraie somme infinie/intégrale dérivée ;16théorèmes+3définitions/19audits standards rapportés,58captures/inputs et3089archives vérifiés. Juge indépendant encore requis, enveloppe Tail SOURCE. Auteur22 :3PASS/8FAIL techniques. Officiel59modules/993auxiliaires conservé, aucune diffusion globale/coefficientN/D_N/WIN.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
