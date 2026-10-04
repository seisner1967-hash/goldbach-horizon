"""Observe one failed compiler run; do not author or run any proof."""
import json, hashlib, re, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role3'; A=P/'stage01_attempt01'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json')
assert r['actual_child_invocations']==1 and r['rows'][0]['exit_code']==1 and not r['victory']
row=r['rows'][0]; assert row['log_sha256']==sha(A/'EpsteinKernel22.log')=='8affa881e01451cff53f978bd16fddddcc1dc4eb83b7fd3cd42c7b6f30f5552a'
assert row['olean_sha256'] is None and r['all_source_inputs_unchanged'] and post['unchanged'] and pre['inputs']==post['inputs']
copies=list((A/'PREEXEC').iterdir()); assert len(copies)==19
for p,input_row in zip(sorted(copies),pre['inputs']): assert sha(p)==input_row['sha256']
kernel_copy=next(p for p in copies if p.name.endswith('_EpsteinKernel22.lean'))
assert sha(kernel_copy)==row['source_sha256']=='cd5cb975242aa38d7d118ac9378409c4bfe406d41227371a7006972d1c145053'
log=(A/'EpsteinKernel22.log').read_text(encoding='utf-8')
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'scope':'ACTUAL_COMPILER_OUTPUT_OBSERVATION_ONLY','actor':'ROLE3','actual_compiler_attempts':1,'actual_Lean_PASS':0,'actual_Lean_FAIL':1,'started':row['started_at'],'finished':row['finished_at'],'exit_code':1,'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'receipt_sha256':sha(A/'receipt.json'),'PREEXEC_sha256':sha(A/'PREEXEC.json'),'POSTEXEC_sha256':sha(A/'POSTEXEC.json'),'compiler_error_diagnostics':len(re.findall(r': error:',log)),'error_classes':['negation/division simplification','one_div versus inverse is not definitional equality','convert derivative equality goal order and redundant no-goal tactics','limit normalization minus one divided by square','factored boundary deficit algebra'],'classification':'TECHNICAL_PROOF_ELABORATION_FAILURE_NOT_PARITY_OR_ANALYTIC_COUNTEREXAMPLE','sorryAx_in_failed_output':'Compiler recovery placeholders appear; source has no admitted proof, exit1 gets zero formal credit.','FULL_root_log':'9ed99b','FULL_root_PRE_POST':'32fa0b','FULL_root_receipt_START':'668004','copies_verified':19,'numeric_unique_G0_AUX_PASS_preserved':True,'official_modules':57,'official_auxiliary_theorems':942,'root_compiler_invocations':0,'victory':False,'next':'Source-only correction, immutable failed source/log preserved, separate FINALsource/builder/preparation FULL+SHA gate before attempt2.'}
(C/'messages/round22_kernel_failure01_observation.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'; insight='Unique G0 numeric24case AUX_PASS retained. First real ROLE3 Kernel author compile07:02:03..07:02:31UTC exit1 with technical proof elaboration errors; immutable source/log captured, noolean/formal credit. GeneratedsorryAx in error recovery excludes allPASS. No parity counterexample. Source repair preparation only; next compiler gate closed. Heat/operator/coefficientN/D_N OPEN; noWin.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — actual first Kernel compile failure\n\n'+insight+'\n\nNumeric24case AUX_PASS is a prior distinct actual newbank, not replayed. Victoryscore0; original57/942 unchanged.\n','--score','0','--insight',insight,'--result','ACTUAL_NUMERIC_AUX_PASS_AND_ONE_TECHNICAL_LEAN_FAIL_SOURCE_REPAIR_PENDING','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_AUX_PASS_KERNEL_FIRST_ACTUAL_LEAN_FAIL_SOURCE_REPAIR_NO_RETRY_GATE'; cp['previous_goal_turn_evidence']+=['round22/role3/stage01_attempt01/receipt.json','round22/role3/stage01_attempt01/EpsteinKernel22.log','.arbor/sessions/parity/.coordinator/messages/round22_kernel_failure01_observation.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='ONE_ACTUAL_KERNEL_LEAN_FAIL_SOURCE_REPAIR_ONLY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
report=B/'REPORT.md'; body=report.read_text(encoding='utf-8'); needle='Aucun module22 n\'a encore été compilé ou certifié par le Juge.'
assert body.count(needle)==1
body=body.replace(needle,'La première invocation Lean22 du noyau réel a échoué à07:02:31UTC avec exit1 : erreurs de simplification et d\'élaboration, source et log conservés, aucun olean ni crédit formel. Une correction en sources est en cours. Aucun module22 n\'a encore compilé avec succès ou été certifié par le Juge.')
report.write_text(body,encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
