"""ROOT metadata closure of independent Gamma factor PASS and paper review."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/judge5/batch05';A=P/'batch05_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'receipt.json')=='090538a9240c53bf248f7c9dbfef3fc708f5de272313e2d4733cb216ad252607'
assert sha(P/'adjudication.md')=='9b49e4c18e172e0a8b1509d72ce9fa1800dfadf2fe83f32233182a7249b3b4e1'
assert sha(P/'completion_receipt.json')=='dc1bcdbbb557d4cbb91367c93fa48a3dc8a234929a9691b5fd0044c0ca516243'
r=read(A/'receipt.json');d=read(P/'completion_receipt.json');pre=read(A/'PREEXEC.json');post=read(A/'POSTEXEC.json');m=read(P/'prepared_manifest.json')
assert r['status']==d['status']=='INDEPENDENT_BATCH05_AUX_PASS' and r['actual_child_invocations']==r['module_count_passed']==2 and r['declarations_passed']==23
assert d['declarations']==23 and d['theorems']==17 and d['definitions']==6 and d['all_current_bytes_preserved']
for flag in ['author_olean_used','hidden_retries','old_batches_recompiled','numeric_bank_replayed','numeric_PASS_used_as_proof','victory','H1_paid','C3_paid','C5_paid','C6_paid','D_N_paid','global_trace_certified']:assert not r[flag],flag
assert pre['inputs']==post['inputs']==m['immutable_inputs'] and len(pre['inputs'])==6707
assert post['all_inputs_unchanged'] and post['gate_unchanged'] and post['captures_unchanged']
assert pre['gate_sha256']==post['gate_sha256']=='2f67e55a754a883208f74b3d5b8fb90818bab45d4c90523d3fdd0bce1642bee6'
assert sha(Path(pre['gate_path']))==pre['gate_sha256']
for row in pre['inputs']:assert sha(Path(row['path']))==row['sha256'],row['path']
assert len(pre['captures'])==32
for row in pre['captures']:assert sha(Path(row['source']))==sha(Path(row['capture']))==row['sha256']
assert pre['protected_archives']==post['protected_archives'] and len(pre['protected_archives'])==3089
for row in pre['protected_archives']:assert sha(B/row['path'])==row['sha256'],row['path']
old=read(P/'closed_judge_bindings.json');assert len(old['inputs'])==209
for row in old['inputs']:assert sha(Path(row['path']))==row['sha256'],row['path']
for row in r['rows']:
 assert row['status']=='INDEPENDENT_LEAN_AUX_PASS' and row['exit_code']==0 and not row['timed_out'] and row['exact_axiom_coverage_standard_only']
 assert sha(A/(row['module']+'.log'))==row['log_sha256'] and sha(A/(row['module']+'.olean'))==row['olean_sha256']
 assert sha(P/'sources'/(row['module']+'.lean'))==row['source_sha256']
review_dir=B/'round22/role3/global_h1_review_source22'
assert sha(review_dir/'review_receipt22.json')=='973da581891aa1c1746999efd7684a88507feaae0e2b83b80197bb01a61217b6'
review=read(review_dir/'review_receipt22.json');assert review['status']=='SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED' and not review['unresolved_blockers'] and review['all_14_bindings_unchanged']
assert sha(Path(review['review_report_path']))==review['review_report_sha256'] and sha(Path(review['domain_addendum_path']))==review['domain_addendum_sha256']
for row in review['bindings']:assert sha(Path(row['path']))==row['sha256'],row['path']
assert not review['structural_PASS_is_enclosure_PASS'] and not review['numeric_PASS'] and not review['WIN']
cpp=C/'checkpoint.json';cp=read(cpp);prior=cp['official_auxiliary_validation'];assert prior['modules']==66 and prior['declarations']==1109
o={'schema':'ROUND22_JUDGE_BATCH05_PASS_ROOT_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'status':r['status'],'receipt_sha256':sha(A/'receipt.json'),'adjudication_sha256':sha(P/'adjudication.md'),
 'ROOT_FULL_reads':{'receipt':'6da6b5','logs':'437133','adjudication_completion':'a94321','numeric_SOURCE_review_and_domains':'8494b5','numeric_SOURCE_receipt':'29d695'},
 'large_PRE_POST_scope':'Completely parsed and bound bytes verified; no raw FULL display',
 'new_modules':2,'new_declarations':23,'official_modules':68,'official_declarations':1132,'includes_definitions':True,
 'Judge22_PASS_modules':11,'Judge22_FAIL_modules':0,'inputs_verified':6707,'oldJudge_files':209,'archives':3089,'captures':32,
 'paid_statement':'Actual weighted Gamma factor box Lipschitz transport, continuity, integrable vertical L1 tail bounded by (27/5)Y^(3/2)exp(-pi*T/4)/(pi/4) under Y>=1,c in[-1/2,3/2],abs(epsilon)=1,T>=0',
 'global_numeric_SOURCE_review_status':review['status'],'numeric_certification_level':review['analytic_certification_level'],
 'global_numeric_run':False,'root_compiler_invocations':0,'root_numeric_invocations':0,
 'H1_paid':False,'C3_paid':False,'C5_paid':False,'C6_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_judge_batch05_pass_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Independent Judge Box12 correctedContour11 actualPASS23, real weightedGamma continuity/Lipschitz/L1 closed continuous tail envelope paid. Official68modules1132auxiliarydeclarations incldefs, Judge22elevenPASS zeroFAIL. Global thermal SOURCE independent paper review closed without blocker; launcher metadata preparing unique ROLE6 run3600s2GiB. GlobalH1/C3/C5/C6/coefficientN/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','GAMMA_FACTOR_AUXILIARY_CERTIFIED_THERMAL_SOURCE_REVIEW_CLOSED','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight]),('update',['--node-id','ROOT','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['official_auxiliary_validation']={'modules':68,'declarations':1132,'includes_definitions':True,'historical_modules':57,'historical_declarations':942,'new_modules':11,'new_declarations':190,'basis':'round22/judge5/batch05/completion_receipt.json','global_D_N_certified':False}
cp['phase']='ROUND22_GAMMA_FACTOR_INDEPENDENT_PASS23_NUMERIC_SOURCE_REVIEW_CLOSED_PREPARING_UNIQUE_RUN'
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==5:actor['status']='BATCH05_CLOSED_TWO_INDEPENDENT_MODULES_PASS23_NO_NEW_COMPILE'
 elif actor['role']==3:actor['status']='ROLE6_NUMERIC_SOURCE_REVIEW_CLOSED_READY_PENDING_PREPARED_GATE'
 elif actor['role']==4:actor['status']='GLOBAL_NUMERIC_LAUNCHER_SOURCE_REVIEW_METADATA_PREPARATION'
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nJuge22 batch05 clos et observé : Box12→premier Contour corrigé11, vrais enfants12:37:05–12:37:50UTC tous exit0/23axiomes standards. Enveloppe continueL1Gamma=(27/5)Y^(3/2)exp(-piT/4)/(pi/4), domaines Y>=1,c[-1/2,3/2],T>=0,abs(epsilon)=1 ; continuité/domination/intégrabilité réellement dérivées.6707inputs/209anciensJuge/3089archives/32captures conservés. Officiel68modules/1132déclarations avec définitions. Revue indépendante producteur numérique close sur papier,14bindings/9runtime stables et domaines explicités ; pas de run/guard numérique effectif. Préparation du lancement uniqueROLE6, limites3600s/2GiB. H1/C3/C5/C6/global/coefficientN/D_N/WIN ouverts.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
