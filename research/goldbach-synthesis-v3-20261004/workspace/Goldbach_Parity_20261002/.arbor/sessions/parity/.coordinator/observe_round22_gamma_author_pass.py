"""Observe genuine Gamma author PASS and conserved bytes; no independent audit at ROOT."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
A=B/'round22/role4/revision02/gamma_attempt3'; M=A.parent/'gamma_prepared_manifest5.json'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); m=read(M)
assert sha(A/'receipt.json')=='87c51cd4e70d8e54d8d1764fb24696b74ccf070e541caa20b7040a3d80feded0'
assert r['status']=='AUTHOR_GAMMA_H2_COMPILE_PASS_PENDING_INDEPENDENT_JUDGE' and r['exit_code']==0 and r['compiler_invocations']==1 and not r['changed_immutable_inputs'] and not r['win']
assert sha(A/'stdout.log')==r['stdout_sha256']=='baea3821834d83192bd3925a2371b3563d6b02d63895cbc3d19622af18753664'
assert sha(A/'GammaPrerequisites22.olean')==r['olean_sha256']=='fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477'
assert sha(A/'stderr.log')==r['stderr_sha256'] and sha(A/'START.json')==r['start_sha256']
assert len(r['captured_inputs'])==13 and len(m['immutable_inputs'])==6442
for e in r['captured_inputs']: assert sha(Path(e['captured']))==e['sha256']==sha(Path(e['original']))
for e in m['immutable_inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert r['archive_after']['checked']==3089 and not r['archive_after']['changed']
archives=read(B/'round22/previous_artifacts_sha256.json'); assert len(archives['sha256'])==3089
for path,digest in archives['sha256'].items(): assert sha(B/path)==digest,path
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'actual_compiler_invocations':1,'started':r['start_utc'],'finished':r['finish_utc'],'exit_code':0,'source_sha256':r['source_sha256'],'stdout_sha256':r['stdout_sha256'],'olean_sha256':r['olean_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':13,'inputs_verified':6442,'archives_verified':3089,'root_FULL_reads':{'stdout_stderr_exit_receipt':'3bfaf7'},'author_reported_standard_prints':23,'author_reported_theorems':20,'author_reported_definitions':3,'independent_Judge_Gamma_credit':False,'author_PASS':4,'author_FAIL':8,'official_modules':59,'official_auxiliary_declarations':993,'H1_Weil_credit':False,'zero_count_credit':False,'D_N_bound':False,'WIN':False,'root_compiler_invocations':0}
with (C/'messages/round22_gamma_author_pass_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
insight='Gamma3 actual author exit0,20theorems3definitions23standard prints,13captures/6442inputs/3089archives conserved. True complex Laplace and rotation decay proved in author; independent Judge still pending. Own21case numeric bank closed without replay. Gamma derivative/box/H1/complete zeros/count/Stieltjes/coefficientN/D_N OPEN,noWin. Official59modules/993auxiliaries unchanged pending audit.'
invoke('record','--node-id','15.2','--raw-report','# Running15.2 — Gamma genuine author PASS\n\n'+insight+'\n','--score','0','--insight',insight,'--result','GAMMA_AUTHOR_AUX_PASS_INDEPENDENT_JUDGE_PENDING','--no-propagate')
invoke('update','--node-id','15.2','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_gamma_author_pass_observation.json')
for actor in cp['in_flight_executors']:
    if actor['role']==4: actor['status']='GAMMA_ACTUAL_AUTHOR_PASS_JUDGE_PENDING_DERIVATIVE_BOX_SOURCE_ONLY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nΓ3 auteur : START08:32:26UTC, FIN08:34:03UTC, exit0 ; vraie Laplace complexe et borne exponentielleΓ prouvées en auteur,20théorèmes+3définitions/23audits standards rapportés.13captures/6442inputs/3089archives vérifiés. Auteur22 :4PASS/8FAIL techniques. Audit indépendant encore requis ; officiel59/993 conservé, H1/coeffN/D_N/WIN non certifiés.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
