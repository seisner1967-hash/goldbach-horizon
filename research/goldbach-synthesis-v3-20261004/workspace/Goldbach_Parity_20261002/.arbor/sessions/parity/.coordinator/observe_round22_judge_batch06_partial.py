"""ROOT observes Judge partial closure metadata; no compiler or evaluator."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/judge5/batch06';A=P/'batch06_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'receipt.json')=='0f1494d07997e45540f0abcb3e553a985ef9b5a8435ae5b267beb990a4b7da2d'
assert sha(P/'adjudication.md')=='eb74f0bf154d86e0967c5b383a02f2fdbbbce999614f861fbbb9270fc075810a'
assert sha(P/'completion_receipt.json')=='3a56827227c8e1f99c288ec54f3f3d1431538de098555c75180f3fffaf6aae68'
r=read(A/'receipt.json');d=read(P/'completion_receipt.json');pre=read(A/'PREEXEC.json');post=read(A/'POSTEXEC.json');m=read(P/'prepared_manifest.json')
assert r['status']==d['status']=='INDEPENDENT_BATCH06_FAILED'
assert r['actual_child_invocations']==2 and r['module_count_passed']==d['modules_passed']==1
assert r['declarations_passed']==d['declarations_passed']==5 and d['theorems_passed']==4 and d['definitions_passed']==1
assert d['modules_failed']==1 and d['modules_not_invoked']==7 and d['all_current_bytes_preserved']
for flag in ['author_olean_used','hidden_retries','old_batches_recompiled','numeric_bank_replayed','numeric_PASS_used_as_proof','victory','H1_paid','C3_paid','C5_paid','C6_paid','D_N_paid','global_trace_certified']:assert not r[flag],flag
assert pre['inputs']==post['inputs']==m['immutable_inputs'] and len(pre['inputs'])==7019
assert post['all_inputs_unchanged'] and post['gate_unchanged'] and post['captures_unchanged']
assert pre['gate_sha256']==post['gate_sha256']=='f7ea9c8de7247c4ae931cae494344d9b98e457616af565dc2ed8437ed4992b0a'
assert sha(Path(pre['gate_path']))==pre['gate_sha256']
for x in pre['inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
assert len(pre['captures'])==64
for x in pre['captures']:assert sha(Path(x['source']))==sha(Path(x['capture']))==x['sha256']
assert pre['protected_archives']==post['protected_archives'] and len(pre['protected_archives'])==3089
for x in pre['protected_archives']:assert sha(B/x['path'])==x['sha256'],x['path']
old=read(P/'closed_judge_bindings.json');assert len(old['inputs'])==270
for x in old['inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
assert [x['module'] for x in r['rows']]==['ZetaEulerDirect22','ZetaReflection22']
for x in r['rows']:
 assert sha(A/(x['module']+'.log'))==x['log_sha256'] and sha(P/'sources'/(x['module']+'.lean'))==x['source_sha256']
 if x['status']=='INDEPENDENT_LEAN_AUX_PASS':
  assert x['exit_code']==0 and x['exact_axiom_coverage_standard_only'] and sha(A/(x['module']+'.olean'))==x['olean_sha256']
 else:assert x['exit_code']==1 and x['olean_sha256'] is None and not (A/(x['module']+'.olean')).exists()
cp_path=C/'checkpoint.json';cp=read(cp_path)
assert cp['official_auxiliary_validation']['modules']==68 and cp['official_auxiliary_validation']['declarations']==1132
o=dict(schema='ROUND22_JUDGE_BATCH06_PARTIAL_ROOT_OBSERVATION',time_utc=datetime.now(timezone.utc).isoformat(),
 status=r['status'],new_modules=1,new_declarations=5,official_modules=69,official_declarations=1137,includes_definitions=True,
 Judge22_PASS_modules=12,Judge22_FAIL_modules=1,noninvoked_modules=7,
 receipt_sha256=sha(A/'receipt.json'),adjudication_sha256=sha(P/'adjudication.md'),completion_sha256=sha(P/'completion_receipt.json'),
 ROOT_FULL_reads=dict(receipt='1dab26',Eulerlog='68cf17',Reflectionlog='664e2d',adjudication='c5ceab',completion='a699c3'),
 inputs_verified=7019,old_judge_files_verified=270,archives_verified=3089,captures_verified=64,
 large_PRE_POST_scope='all entries parsed and every byte hash checked; raw FULL not claimed',
 failure_diagnostic='ROLE5: typed point inference, missing simplification alias/composition, tactic after closed goal; no mathematical parity counterexample',
 failed_module_credit=0,ROOT_Lean_invocations=0,ROOT_numeric_invocations=0,H1_paid=False,C5_global_paid=False,D_N_paid=False,WIN=False)
path=C/'messages/round22_judge_batch06_partial_observation.json'
with path.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Judge06 closed partial1PASS5 Euler true zeta right nonvanishing from paid Euler convergence. Reflection54e32a actualFAIL API typedpoint/alias/composition/closedgoal; zero credit,7notinvoked, no mathematical paritycounterexample. Official69/1137 incldefs, Judge22 12PASS1FAIL. 7019inputs270oldJudge3089archives64captures preserved. NewReflection07SOURCEcc39bd uncompiled, future8module83 gate pending; globalnumeric unique active fixedlimits, H1/C5global/additiveN/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','PARTIAL_EULER_AUX_PASS_REFLECTION_API_FAIL','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['official_auxiliary_validation']=dict(modules=69,declarations=1137,includes_definitions=True,historical_modules=57,historical_declarations=942,new_modules=12,new_declarations=195,basis='round22/judge5/batch06/completion_receipt.json',global_D_N_certified=False)
cp['phase']='ROUND22_C5_REFLECTION_API_FAIL_REPAIR07_GLOBAL_NUMERIC_RUNNING'
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(path.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==5:actor['status']='BATCH06_CLOSED_PARTIAL1PASS5_ONEAPI_FAIL_PREPARING07'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nJuge22 batch06 clos : EulerDirect indépendant PASS5 (4 théorèmes,1def), puis Reflection54e32a FAIL technique aux lignes94/124/131 ; sept aval NONINVOQUÉS. Aucun crédit des prints de récupération, aucun diagnostic de réfutation/parité. Deux enfants13:06:18–13:06:57UTC, source0d790e/olean555b10 Euler, dix erreursReflection sansolean ; ancienFAIL préservé.7019inputs/270anciensJuge/3089archives/64captures intacts vérifiés ROOT. Officiel69modules/1137déclarations avecdefs. Reflection07 corrigéecc39bd SOURCE noncompilée, prochainlot8/83 prépare. Calculnumérique global unique poursuit son cataloguefixe et limites ; H1/C5global/coefficientN/D_N/WIN ouverts.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
