"""ROOT metadata observation only: bind closed Judge evidence, update ledger."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/judge5/batch04/three_modules';A=P/'batch04_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'receipt.json')=='228b0958ecac8037e1776cf5cc32db340a8f52944c1e9cd398415dd9f0415c5d'
assert sha(P/'adjudication.json')=='d227ca049382b1cb0948736c58fc75f65c1557a94e9f554c025167253bf64a7d'
assert sha(P/'completion.md')=='741983eec1a816cc5644ba4381eb93c6c4a7a3f4204221161ef1320af3e82592'
r=read(A/'receipt.json');d=read(P/'adjudication.json')
pre=read(A/'PREEXEC.json');post=read(A/'POSTEXEC.json');m=read(P/'prepared_manifest.json')
assert r['status']==d['status']=='INDEPENDENT_BATCH04_AUX_PASS'
assert r['actual_child_invocations']==r['module_count_passed']==3 and r['declarations_passed']==52
assert r['rows']==d['rows'] and d['theorem_count']==44 and d['definition_count']==8
for flag in ['author_olean_used','hidden_retries','old_batches_recompiled','numeric_bank_replayed','numeric_PASS_used_as_proof','victory','H1_paid','C3_paid','C5_paid','D_N_paid','global_trace_certified']:assert not r[flag],flag
assert pre['inputs']==post['inputs']==m['immutable_inputs'] and len(pre['inputs'])==6648
assert post['all_inputs_unchanged'] and post['gate_unchanged'] and post['captures_unchanged']
assert pre['gate_sha256']==post['gate_sha256']=='66b47ab7d2d5ada4a81d8a34c2354c26967d2bd7997064d77f32757b5dc1040a'
assert sha(Path(pre['gate_path']))==pre['gate_sha256']
for row in pre['inputs']:assert sha(Path(row['path']))==row['sha256'],row['path']
assert len(pre['captures'])==26
for row in pre['captures']:assert sha(Path(row['source']))==sha(Path(row['capture']))==row['sha256']
assert pre['protected_archives']==post['protected_archives'] and len(pre['protected_archives'])==3089
for row in pre['protected_archives']:assert sha(B/row['path'])==row['sha256'],row['path']
old=read(P/'closed_judge_bindings.json');assert len(old['inputs'])==134
for row in old['inputs']:assert sha(Path(row['path']))==row['sha256'],row['path']
for row in r['rows']:
 assert row['status']=='INDEPENDENT_LEAN_AUX_PASS' and row['exit_code']==0 and not row['timed_out'] and row['exact_axiom_coverage_standard_only']
 assert sha(A/(row['module']+'.log'))==row['log_sha256']
 assert sha(A/(row['module']+'.olean'))==row['olean_sha256']
 assert sha(P/'sources'/(row['module']+'.lean'))==row['source_sha256']
for row in d['artifacts']:assert sha(Path(row['path']))==row['sha256'],row['path']
cpp=C/'checkpoint.json';cp=read(cpp);prior=cp['official_auxiliary_validation']
assert prior['modules']==63 and prior['declarations']==1057
o={'schema':'ROUND22_JUDGE_BATCH04_PASS_ROOT_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'status':r['status'],'receipt_sha256':sha(A/'receipt.json'),'adjudication_sha256':sha(P/'adjudication.json'),
 'root_FULL_reads':{'receipt':'54cf58','logs':'a55b41','adjudication_parts':['59f128','00a3ed'],'completion':'8d442d'},
 'PRE_POST_scope':'Complete JSON parsed/equality and all bytes checked; no FULL raw display',
 'new_modules':3,'new_declarations':52,'official_modules':66,'official_declarations':1109,'includes_definitions':True,
 'Judge22_PASS_modules':9,'Judge22_FAIL_modules':0,'input_count':6648,'captures':26,'oldJudge_files':134,'archives':3089,
 'paid_statement':d['paid_statement'],'root_compiler_invocations':0,'root_numeric_invocations':0,
 'H1_paid':False,'C3_paid':False,'C5_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_judge_batch04_pass_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Independent Judge PsiCore19 BetaLimit23 Integral10 actualPASS52: true Gamma logarithmic derivative integral and integrability on Re(z)>0, no unpaid target hypotheses. Official66modules1109auxiliarydeclarations incldefs; Judge22ninePASS zeroFAIL. GlobalH1/C3/C5/coefficientN/D_N/WIN open. Global numeric SOURCE writerROLE4/reviewerROLE3 active; no globalN run.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','PSI_P1_AUXILIARY_CERTIFIED_GLOBAL_OPEN','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight]),('update',['--node-id','ROOT','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['official_auxiliary_validation']={'modules':66,'declarations':1109,'includes_definitions':True,'historical_modules':57,'historical_declarations':942,'new_modules':9,'new_declarations':167,'basis':'round22/judge5/batch04/three_modules/adjudication.json','global_D_N_certified':False}
cp['phase']='ROUND22_PSI_P1_INDEPENDENT_PASS52_GLOBAL_NUMERIC_SOURCE_WRITER_REVIEWER'
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==5:actor['status']='BATCH04_CLOSED_THREE_INDEPENDENT_MODULES_PASS52_NO_NEW_COMPILE'
 elif actor['role']==3:actor['status']='C5_SOURCE_CHECKPOINT_PRESERVED_ROLE6_GLOBAL_NUMERIC_SOURCE_REVIEW'
 elif actor['role']==4:actor['status']='ANALYTIC02_PARTIAL_CLOSED_GLOBAL_NUMERIC_SOURCE_WRITER'
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nJuge22 batch04 clos : trois modules PsiCore19, BetaLimit23, Integral10 réellement recompilés indépendamment11:40:20–11:41:42UTC, tous exit0/52axiomes standards. P1 : vraie formule intégrale de Γ′/Γ pour Re(z)>0 avec intégrabilité, majorant construit, DCT et Jacobien réel. Conservation6648entrées/134anciensJuge/3089archives/26captures vérifiée ROOT. Officiel66modules/1109déclarations auxiliaires incluant définitions. H1,C3,C5 global,coefficientN,D_N et WIN ouverts. Aucun nouveau calcul globalN. ROLE4 écrit le nouveau producteur/checker ; ROLE3 assure le contrôle SOURCE numérique indépendant.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
