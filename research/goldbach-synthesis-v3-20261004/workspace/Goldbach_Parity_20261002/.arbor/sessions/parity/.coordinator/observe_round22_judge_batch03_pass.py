"""Record the independent Judge verdict and pure byte conservation."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/judge5/batch03';A=P/'batch03_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'receipt.json')=='74959436b372e6dc180b1f5b79e51e17bded56361ba70774695a906dc3f3d4ee'
assert sha(P/'adjudication.json')=='118b44ffe66198ccfeaa477f9c57e7d06fb681dbc83a06207cceae79a680df50'
assert sha(P/'completion.md')=='ace8df285c3b2693a22a96f323fa3587d36ba204c46a161d1695663c78306a8d'
r=read(A/'receipt.json');pre=read(A/'PREEXEC.json');post=read(A/'POSTEXEC.json');m=read(P/'prepared_manifest.json');d=read(P/'adjudication.json')
assert r['status']==d['status']=='INDEPENDENT_BATCH03_AUX_PASS' and r['actual_child_invocations']==r['modules_passed']==1 and r['declarations_passed']==8
assert not r['author_olean_used'] and not r['hidden_retries'] and not r['old_batches_recompiled'] and not r['victory']
assert pre['inputs']==post['inputs']==m['immutable_inputs'] and len(pre['inputs'])==6597
assert post['all_inputs_unchanged'] and post['gate_unchanged'] and post['captures_unchanged']
for row in pre['inputs']:assert sha(Path(row['path']))==row['sha256'],row['path']
assert len(pre['captures'])==21
for row in pre['captures']:assert sha(Path(row['source']))==sha(Path(row['capture']))==row['sha256']
assert pre['protected_archives']==post['protected_archives'] and len(pre['protected_archives'])==3089
for row in pre['protected_archives']:assert sha(B/row['path'])==row['sha256']
old=read(P/'closed_judge_bindings.json');assert len(old['inputs'])==90
for row in old['inputs']:assert sha(Path(row['path']))==row['sha256']
for row in r['rows']:
 assert row['status']=='INDEPENDENT_LEAN_AUX_PASS' and row['exit_code']==0 and row['exact_axiom_coverage_standard_only']
 for key,suffix in [('stdout_sha256','.stdout.log'),('stderr_sha256','.stderr.log'),('olean_sha256','.olean')]:assert sha(A/(row['module']+suffix))==row[key]
cpp=C/'checkpoint.json';cp=read(cpp);prior=cp['official_auxiliary_validation'];assert prior['modules']==62 and prior['declarations']==1049
o={'schema':'ROUND22_JUDGE_BATCH03_PASS_ROOT_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'status':r['status'],'receipt_sha256':sha(A/'receipt.json'),'adjudication_sha256':sha(P/'adjudication.json'),
 'root_FULL_reads':{'receipt_and_log':'90c4ea','adjudication_completion':'0c028c'},
 'PRE_POST_scope':'Complete JSON parsed/equality and allbytes checked; no FULL raw display',
 'new_modules':1,'new_declarations':8,'official_modules':63,'official_declarations':1057,'includes_definitions':True,
 'Judge22_PASS_modules':6,'Judge22_FAIL_modules':0,'input_count':6597,'captures':21,'oldJudge_files':90,'archives':3089,
 'paid_statement':d['paid_statement'],'root_compiler_invocations':0,'root_numeric_invocations':0,'H1_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_judge_batch03_pass_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Independent Judge GammaDerivative actualPASS8: real Gamma Cauchy derivative envelope normGammaPrime<=19exp(-piabsIm/4) on Re1..2, no target premises. Official63modules1057auxiliarydeclarations incldefs, Judge22sixPASS zeroFAIL; globalH1/C3/C5/coefficientN/D_N/WIN open. Core19 separate sourceaudit preparing; numericR01closedaux46cases19mutants no globaltest.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.2','--raw-report',insight,'--score','0','--insight',insight,'--result','GAMMA_DERIVATIVE_AUXILIARY_CERTIFIED_GLOBAL_OPEN','--no-propagate']),('update',['--node-id','15.2','--status','running','--insight',insight]),('update',['--node-id','ROOT','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['official_auxiliary_validation']={'modules':63,'declarations':1057,'includes_definitions':True,'historical_modules':57,'historical_declarations':942,'new_modules':6,'new_declarations':115,'basis':'round22/judge5/batch03/adjudication.json','global_D_N_certified':False}
cp['last_progress']=insight
cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==5:actor['status']='BATCH03_CLOSED_INDEPENDENT_GAMMA_DERIVATIVE_PASS_CORE19_NEW_STAGE_SOURCE'
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nJuge22 batch03 : ΓDerivative seul réellement compilé11:15:36–11:16:13UTC, exit0/8axiomes standards ; vraie borne Γ′ et Cauchy certifiés. Conservation6597entrées/90anciensJuge/3089archives/21captures. Officiel63modules/1057déclarations auxiliaires incluant définitions. Aucun crédit H1,C3/C5,coefficientN,D_N ou WIN.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
