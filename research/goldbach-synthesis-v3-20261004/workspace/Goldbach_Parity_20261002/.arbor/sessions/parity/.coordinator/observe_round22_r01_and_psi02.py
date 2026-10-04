"""ROOT records closed actor verdicts; metadata only, no numerical checker."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role6/thermal_h1/revision01';A=P/'actual_r01'
Q=B/'round22/role3/h1_psi/revision02/psi_batch02_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'actual_receipt.json');data=read(A/'result_r01.json');p=read(P/'preparation_r01.json');post=read(A/'POSTEXEC_integrity.json')
assert sha(A/'actual_receipt.json')=='675fd4efcb6fc038b142c89eb6ff7843d57072a596e144cb52e8c681bdb76500'
assert sha(A/'result_r01.json')==r['result_sha256']=='c43622616022e65991aee5a12d189d3bae142db1f2d347cb131e8abd685c7a6c'
assert sha(A/'actual.log')==r['log_sha256']=='97d4abaca2a3767297a524b8aba1c00f7b064d0c1b1324ba831c53f2463c4dd4'
assert r['exit_code']==0 and r['launch_error'] is None and r['post_integrity']
assert data['status']==data['verdict']=='THERMAL_COMPONENT_R01_AUX_PASS'
assert len(data['cases'])==46 and len(data['mutations'])==19
assert not data['failures'] and not data['unresolved']
assert data['independent_checker']['checker_PASS'] and not data['independent_checker']['checker_errors']
assert not any(data[k] for k in ('H1_numeric_claim','H1_formal_claim','coefficient_N_claim','D_N_claim','WIN','previous_incomplete_values_used_as_oracle'))
assert data['old_bank_replays']==0
assert post['all_unchanged'] and post['preparation_unchanged'] and post['gate_unchanged']
assert len(post['bindings'])==len(p['bindings'])==33
for x in p['bindings']:
    q=Path(x['path']);assert sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],x['path']
captures=read(A/'PREEXEC_captures.json')['captures'];assert len(captures)==35
for x in captures:assert sha(Path(x['copy']))==x['sha256'],x['copy']
assert sha(A/'sqrt_certificates_r01.jsonl')==r['sqrt_certificate_sha256']=='553cd8b9debcbacce4b68696e636d5a692bdcde0a39630f4b524eeb98f7e6e77'
assert len((A/'sqrt_certificates_r01.jsonl').read_text(encoding='utf-8').splitlines())==15
assert sha(Q/'receipt.json')=='0961062ade0d902dcd6f377ba23ccac67021187d32bdc68e4c14c94ed1aa724b'
assert sha(Q/'GammaPsiCore22.log')=='98abb8afebf7bb1c0594cafd6f8320c3cdfb2d4dbe5a0280141821188642d470'
qr=read(Q/'receipt.json');qp=read(Q/'POSTEXEC.json')
assert qr['actual_child_invocations']==1 and qr['rows'][0]['exit_code']==1 and qr['rows'][0]['olean_sha256'] is None
assert qr['all_inputs_unchanged'] and qp['all_inputs_unchanged']
assert len(qp['inputs'])==56 and len(qp['cache_artifacts_hash_only_readonly'])==6476
for x in qp['inputs']+qp['cache_artifacts_hash_only_readonly']:assert sha(Path(x['path']))==x['sha256'],x['path']
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,expected in archives['sha256'].items():assert sha(B/rel)==expected,rel
o={'schema':'ROUND22_R01_AUX_PASS_PSI02_TECHNICAL_FAILURE_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'numeric_status':data['status'],'numeric_START':r['actual_START'],'numeric_FINISH':r['actual_FINISH'],
 'numeric_receipt_sha256':sha(A/'actual_receipt.json'),'numeric_result_sha256':sha(A/'result_r01.json'),
 'numeric_cases':46,'numeric_mutations':19,'numeric_caps_verified':35,'isqrt_lines':15,
 'result_read_scope':'Complete235516byteJSON parsed; header projection6eb240 and receipt/logFULL26e3ce; no FULL raw result or independent numerical recomputation claim',
 'POST_FULL_read':'caf98c','psi02_FULL_read':'56f2dd','psi02_status':'CORE_TECHNICAL_PARSER_FAILURE_NO_MODULE_PASS',
 'psi02_START':qr['rows'][0]['started_at'],'psi02_FINISH':qr['rows'][0]['finished_at'],
 'psi02_failure':'unexpected .. at integral bound;18 standard prints/1generated sorryAx, no olean,3NOT_INVOKED',
 'psi02_inputs_verified':56,'cache_artifacts_verified':6476,'archives_verified':3089,
 'root_numeric_invocations':0,'root_Lean_invocations':0,'official_modules':62,'official_declarations':1049,
 'H1_global_certified':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_r01_and_psi02_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Distinct R01 real auxiliary PASS46cases/19mutants,35captures/33bindings intact; full thermalN not executed. Psi02 Core exit1 due integral parser unexpected ..,18standardprints/1generatedsorryAx/noolean,3notinvoked. No formula counterexample established. Psi03 SOURCE correction pending distinct gate; official62/1049 unchanged; globalH1/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','COMPONENT_R01_AUX_PASS_PSI02_PARSER_FAILURE','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
    child=subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cpp=C/'checkpoint.json';cp=read(cpp)
cp['phase']='ROUND22_COMPONENT_R01_AUX_PASS_CLOSED_PSI02_PARSER_FAILURE_PSI03_SOURCE_JUDGE_GAMMA_DERIVATIVE_PENDING'
cp['last_progress']=insight
for a in cp['in_flight_executors']:
    if a['role']==3:a['status']='PSI02_CLOSED_PARSER_FAIL_PSI03_SOURCE'
    if a['role']==6:a['status']='THERMAL_COMPONENT_R01_AUX_PASS_CLOSED_NO_REPLAY'
cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nR01 thermique auxiliaire : exécution unique10:41:16–10:44:48UTC, exit0,46cas/19mutations/15certificatsisqrt,33bindings/35captures intacts ; résultatc436226…. Ne constitue pasle testcompletN=10^8. ψ02 : Core seul10:45:24–10:45:55UTC exit1, parseurintégrale unexpected ..,18printsstandards/1sorryAxgénéré/aucunolean,3suivants noninvoqués. Révision03 distincte SOURCE. Officiel62/1049inchangé,H1/D_N/WINouverts.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
