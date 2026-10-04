"""Observe genuine Gamma second failure and immutable bytes; coordinator metadata only."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
A=B/'round22/role4/revision01/gamma_attempt2'; M=B/'round22/role4/revision01/gamma_prepared_manifest4.json'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); m=read(M)
assert sha(A/'receipt.json')=='5ebfd56de12c3b3e01342a3dbf73690a5a24c66a9d1eb11aa1e449b6c8e8070f'
assert r['exit_code']==1 and r['compiler_invocations']==1 and r['olean_sha256'] is None and not r['changed_immutable_inputs'] and not r['win']
assert sha(A/'stdout.log')==r['stdout_sha256']=='4c2790f81b08e622cb8b970fab77edce0214f12a228e0ddd60f98d21c5cd614f'
assert sha(A/'stderr.log')==r['stderr_sha256'] and sha(A/'START.json')==r['start_sha256']
assert len(r['captured_inputs'])==13 and len(m['immutable_inputs'])==6415
for e in r['captured_inputs']: assert sha(Path(e['captured']))==e['sha256']==sha(Path(e['original']))
for e in m['immutable_inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert r['archive_after']['checked']==3089 and not r['archive_after']['changed']
archives=read(B/'round22/previous_artifacts_sha256.json')
assert len(archives['sha256'])==3089
for path,digest in archives['sha256'].items(): assert sha(B/path)==digest,path
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'actual_compiler_invocations':1,'started':r['start_utc'],'finished':r['finish_utc'],'exit_code':1,'source_sha256':r['source_sha256'],'stdout_sha256':r['stdout_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':13,'inputs_verified':6415,'archives_verified':3089,'root_FULL_reads':{'stdout':'61c915','receipt':'d5da3f+6b655b'},'error_lines':[202],'error_count':1,'actor_diagnosis':'Complex.ofReal_mul rewrite pattern already eliminated by preceding change; five other technical corrections accepted.','generated_sorryAx_formal_credit':False,'analytic_or_parity_refutation_claim':False,'Gamma_formal_credit':False,'author_PASS':2,'author_FAIL':8,'official_modules':59,'official_auxiliary_declarations':993,'WIN':False,'root_compiler_invocations':0}
with (C/'messages/round22_gamma_failure02_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
insight='Gamma second actual compiler exit1 one local rewrite error,13captures/6415inputs/3089archives conserved; no olean, no Gamma formal credit. Own21case numeric bank remains closed AUX_PASS. Distinct revision02 source and gate3 required. Official59modules/993auxiliaries after independent Kernel/Finite, global Weil/zeros/coefficientN/D_N OPEN,noWin.'
invoke('record','--node-id','15.2','--raw-report','# Running15.2 — Gamma second technical failure\n\n'+insight+'\n','--score','0','--insight',insight,'--result','GAMMA_SECOND_ACTUAL_TECHNICAL_FAIL_REVISION02_SOURCE','--no-propagate')
invoke('update','--node-id','15.2','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_gamma_failure02_observation.json')
for actor in cp['in_flight_executors']:
    if actor['role']==4: actor['status']='GAMMA_SECOND_TECHNICAL_FAIL_REVISION02_PREPARED_GATE_PENDING'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nΓ auteur2 : START08:13:37UTC, FIN08:15:13UTC, exit1, une erreur de réécriture ligne202, aucun olean ;13captures/6415inputs/3089archives vérifiés. Révision02 distincte préparée, aucun crédit formelΓ ni verdict de parité. Auteur22 :2PASS/8FAIL techniques ; officiel59modules/993auxiliaires après Juge Kernel/Finite.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
