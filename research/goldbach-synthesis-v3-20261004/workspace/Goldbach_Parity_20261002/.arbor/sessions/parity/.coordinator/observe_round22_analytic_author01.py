"""ROOT observed author outcomes; hashes and bookkeeping only, no Judge audit."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role4/h1_contour/analytic_batch01';A=P/'actual_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json');m=read(P/'prepared_manifest22.json');post=read(A/'POSTEXEC.json')
assert r['status']=='AUTHOR_ANALYTIC_BATCH_FAIL' and r['actual_child_invocations']==2
assert r['stop_first_failure'] and r['retry_count']==0 and not r['changed_inputs']
assert [x['module'] for x in r['rows']]==['GammaDerivative22','GammaBoxBounds22']
assert r['rows'][0]['exit_code']==0 and r['rows'][0]['exact_standard_axiom_coverage']
assert r['rows'][1]['exit_code']==1 and r['rows'][1]['olean_sha256'] is None
assert r['modules_not_launched']==['GammaContourComponent22','MellinThermal22','MellinThermalInversion22']
assert post['bindings_checked']==6517 and not post['changed_inputs']
for x in r['rows']:
    assert sha(A/(x['module']+'.stdout.log'))==x['stdout_sha256']
    assert sha(A/(x['module']+'.stderr.log'))==x['stderr_sha256']
    if x['olean_sha256']:assert sha(A/(x['module']+'.olean'))==x['olean_sha256']
for x in m['immutable_inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
for x in r['captures']:assert sha(Path(x['captured']))==x['sha256'],x['captured']
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,expected in archives['sha256'].items():assert sha(B/rel)==expected,rel
o={'schema':'ROUND22_ANALYTIC_AUTHOR01_OBSERVATION','observed_utc':datetime.now(timezone.utc).isoformat(),
 'receipt_sha256':sha(A/'receipt.json'),'root_FULL_reads':{'receipt':'7dc465','box_log_and_POST':'c20b7a'},
 'author_PASS_modules':['GammaDerivative22'],'author_PASS_declarations_pending_Judge':8,
 'author_FAIL_modules':['GammaBoxBounds22'],'not_invoked':r['modules_not_launched'],
 'failure_classification':'Lean API neighborhood mismatch, not an arithmetic counterexample or parity deduction failure',
 'verified_inputs':6517,'verified_captures':len(r['captures']),'verified_archives':3089,
 'root_compiler_invocations':0,'root_math_invocations':0,'official_modules':62,'official_declarations':1049,
 'global_H1_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_analytic_author01_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='GammaDerivative22 author PASS8 pending independent Judge. GammaBoxBounds22 exit1: differentiableAt expects membership in neighborhood but receives IsOpen;3 following modules not invoked.6517bindings/3089archives unchanged. Distinct GammaBox SOURCE revision, no author PASS replay. Global H1/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command,args in [('record',['--node-id','15.2','--raw-report',insight,'--score','0','--insight',insight,'--result','ANALYTIC_AUTHOR01_PARTIAL_PASS_API_FAILURE_PENDING_JUDGE','--no-propagate']),('update',['--node-id','15.2','--status','running','--insight',insight])]:
    p=subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert p.returncode==0,(p.stdout,p.stderr)
cpp=C/'checkpoint.json';cp=read(cpp)
cp['phase']='ROUND22_ANALYTIC_AUTHOR01_CLOSED_PARTIAL_PASS_JUDGE_PENDING_PSI02_AND_NUMERIC_R01_RUNNING'
for a in cp['in_flight_executors']:
    if a['role']==4:a['status']='GAMMA_DERIVATIVE_AUTHOR_PASS_PENDING_JUDGE_BOX_SOURCE_REVISION'
    if a['role']==3:a['status']='PSI_BATCH02_RUNNING'
    if a['role']==6:a['status']='THERMAL_COMPONENT_R01_RUNNING'
cp['root_bookkeeping_incidents_round22'].append({'kind':'UNCONSUMED_ANALYTIC_GATE_RECEIPT_FIELD_CORRECTION','initial_SHA':'15302a4d8f850c9c5f4e5135181dae05101612fa784c28a497f6269ce6051c78','corrected_SHA':'39c59e2c33ecbb4682cc2c0bd8b264b1b22b92d06057ba6993003ea66d500f55','no_launcher_before_correction':True})
cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nΓ–Mellin auteur01 : ΓDerivative PASS auteur8déclarations10:40:22–10:40:59UTC, en attenteJuge. ΓBox FAIL10:40:59–10:41:21UTC (APIvoisinage),3suivants noninvoqués.6517inputs/3089archives intacts. GateROOT initiale erronée corrigée avant toute invocation, versioninitiale conservée ; incident de contrôle, pasFAILLean. Officiel62modules/1049déclarations inchangé ; H1/D_N/WIN ouverts.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
