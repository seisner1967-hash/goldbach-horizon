"""Observe one real author failure and preserve scope; metadata only."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round22/role3/stage02/stage02_attempt01'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); row=r['rows'][0]
assert r['actual_child_invocations']==1 and row['exit_code']==1 and row['olean_sha256'] is None and not r['victory']
assert row['log_sha256']==sha(A/'EpsteinFinite22.log')=='28397f513fdeac16b40385e057add160964585fde61e54ee22f31424425de9df'
assert pre['inputs']==post['inputs'] and len(pre['inputs'])==21 and post['unchanged'] and r['all_source_inputs_unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==21
for p,entry in zip(copies,pre['inputs']): assert sha(p)==entry['sha256']==sha(Path(entry['path']))
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'scope':'ACTUAL_AUTHOR_OUTPUT_AND_BYTE_OBSERVATION_ONLY','actor':'ROLE3','actual_new_child_invocations':1,'cumulative_author_Lean_PASS':1,'cumulative_author_Lean_FAIL':2,'stage':'G0_FINITE_STAGE02','started':row['started_at'],'finished':row['finished_at'],'exit_code':1,'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'receipt_sha256':sha(A/'receipt.json'),'PREEXEC_sha256':sha(A/'PREEXEC.json'),'POSTEXEC_sha256':sha(A/'POSTEXEC.json'),'copies_verified':21,'FULL_root_log':'2d46e7','FULL_root_receipt':'1b4568','FULL_root_START':'9cf591','PRE_POST_scope':'Parsed metadata and every bound copy verified, not FULL text displayed','error_classes':['Continuous.const_mul API absent','integral_const_mul rewrite leaves True-or-weight-zero obligation','Int.negSucc coercion normalization'],'classification':'TECHNICAL_ELABORATION_NOT_ANALYTIC_OR_PARITY_REFUTATION','Kernel_author_PASS_preserved':True,'unique_G0_numeric_AUX_PASS_preserved':True,'independent_judge':False,'official_modules':57,'official_auxiliary_theorems':942,'root_compiler_invocations':0,'D_N_bound':False,'victory':False,'next':'Separate source revision and fresh gate after FULL+SHA review; no automatic retry.'}
target=C/'messages/round22_finite_failure01_observation.json'
with target.open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
obs['diagnostic_refinement']='ROLE3 source-read confirms integral_const_mul is unconditional; True-or-weight-zero is residual endpoint/algebra normalization, not an unpaid analytic hypothesis.'
insight='Actual G0 numeric24case AUX_PASS and authorKernel PASS retained. First Finite compile07:21:53..07:22:16UTC exit1,3technicalAPI/coercion/secondary-goal errors,noolean,21inputs unchanged; no analytic/parity counterexample. integral_const_mul is unconditional; residual True-or-weight-zero is final algebra normalization. Round22 author1PASS2FAIL. Separate source correction only and next gate closed; independentJudge/fullunfold/tail/coefficientN/D_N OPEN; noWin.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — actual finite-window technical failure\n\n'+insight+'\n','--score','0','--insight',insight,'--result','G0_NUMERIC_AUX_PASS_KERNEL_AUTHOR_PASS_FINITE_TECHNICAL_FAIL_REPAIR_PENDING','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_KERNEL_AUTHOR_PASS_FINITE_FIRST_FAIL_SOURCE_CORRECTION_GAMMA_BANK_PREPARATION'
cp['previous_goal_turn_evidence']+=['round22/role3/stage02/stage02_attempt01/receipt.json','round22/role3/stage02/stage02_attempt01/EpsteinFinite22.log','.arbor/sessions/parity/.coordinator/messages/round22_finite_failure01_observation.json']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='FINITE_TECHNICAL_FAIL_SEPARATE_SOURCE_CORRECTION_ONLY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nFenêtre finie22, première invocation réelle : exit1 à07:22:16UTC, trois erreurs techniques (API continuité, obligation de réécriture, coercition Int.negSucc), aucun olean. Les21captures et inputs sont inchangés. Noyau auteurPASS conservé ; correction distincte en sources, aucun crédit de parité/globalD_N.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
