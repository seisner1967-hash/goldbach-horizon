"""Pure metadata observation of two closed partial author batches."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
P=B/'round22/role3/h1_psi/revision04/psi_batch04_attempt01';Q=B/'round22/role4/h1_contour/analytic_batch02/actual_attempt01'
assert sha(P/'receipt.json')=='73580f763b089606dbe488720d86920658dacad1b100657c26b9c8cc2cf4209b'
assert sha(Q/'receipt.json')=='d0bb6fda4cbdb187bea72c72423764a888c6a9cbd8ba87112e9d2519184dcbab'
r=read(P/'receipt.json');s=read(Q/'receipt.json');post=read(P/'POSTEXEC.json')
assert r['actual_child_invocations']==3 and [x['exit_code'] for x in r['rows']]==[0,0,1] and r['all_inputs_unchanged']
assert len(post['inputs'])==74 and len(post['cache_artifacts_hash_only_readonly'])==6476 and post['all_inputs_unchanged']
for x in post['inputs']+post['cache_artifacts_hash_only_readonly']:assert sha(Path(x['path']))==x['sha256'],x['path']
for x in r['rows']:
 assert sha(P/(x['module']+'.log'))==x['log_sha256']
 if x['olean_sha256']:assert sha(P/(x['module']+'.olean'))==x['olean_sha256']
assert s['actual_child_invocations']==2 and [x['exit_code'] for x in s['rows']]==[0,1] and s['changed_inputs']==[] and s['retry_count']==0
assert s['modules_not_launched']==['MellinThermal22','MellinThermalInversion22']
m=read(Q.parent/'prepared_manifest22.json');assert len(m['immutable_inputs'])==6524
for x in m['immutable_inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
assert len(s['captures'])==24
for x in s['captures']:assert sha(Path(x['original']))==sha(Path(x['captured']))==x['sha256']
for x in s['rows']:
 for key,suffix in [('stdout_sha256','.stdout.log'),('stderr_sha256','.stderr.log')]:assert sha(Q/(x['module']+suffix))==x[key]
 if x['olean_sha256']:assert sha(Q/(x['module']+'.olean'))==x['olean_sha256']
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,digest in archives['sha256'].items():assert sha(B/rel)==digest,rel
o={'schema':'ROUND22_PSI04_ANALYTIC02_PARTIAL_AUTHOR_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'receipts':[sha(P/'receipt.json'),sha(Q/'receipt.json')],'ROOT_FULL_reads':{'psi_receipt':'c0c379','Dup_log':'f5f546','analytic_receipt':'a71330','Contour_log':'f5c6c8'},
 'author_PASS_pending_judge':{'Beta':23,'Integral_P1':10,'GammaBox':12},'author_technical_FAIL_modules':['Duplication','GammaContour'],
 'Dup_diagnostic':'four tactic errors: numeral projections, unreduced comp/id, quotient inverse simplification',
 'Contour_diagnostic':'ContinuousAt.comp base point inference; absent Real.integral_exp_neg_Ioi and rewrite cascade',
 'Mellin_modules_not_invoked':2,'psi_inputs_verified':74,'psi_cache_verified':6476,'analytic_inputs_verified':6524,'analytic_captures_verified':24,'archives_verified':3089,
 'official_count_delta':0,'root_compiler_invocations':0,'root_numeric_invocations':0,'H1_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_psi04_analytic02_partial_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Psi04 Beta23/Integral10 actual authorPASS pending Judge; Dup2 failed on four tactic normalizations. Analytic02 GammaBox12 authorPASS pending Judge; Contour failed on comp basepoint and absent integral API, two Mellin modules NOTINVOKED. Full globalthermal numericSOURCE review is next priority; no false parity or H1/D_N/WIN credit.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','PSI_P1_AND_GAMMA_BOX_AUTHOR_PASS_GLOBAL_OPEN','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cpp=C/'checkpoint.json';cp=read(cpp);cp['last_progress']=insight;cp['phase']='ROUND22_PSI_P1_AUTHOR_PASS_INDEPENDENT_STAGE52_SOURCE_NUMERIC_GLOBAL_SOURCE_REVIEW'
for a in cp['in_flight_executors']:
 if a['role']==3:a['status']='PSI04_CLOSED_BETA23_INTEGRAL10_AUTHOR_PASS_DUP_FAIL_DUP05_SOURCE'
 if a['role']==4:a['status']='ANALYTIC02_CLOSED_BOX12_AUTHOR_PASS_CONTOUR_FAIL_GLOBAL_NUMERIC_SOURCE_REVIEW'
 if a['role']==5:a['status']='NEW_PSI52_INDEPENDENT_STAGE_PREPARING'
cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nψ04 : Beta23 et Integral10 (vraie P1) auteur PASS, Dup2 FAIL technique ;3enfants uniques11:21:53–11:22:58UTC. Analytique02 : ΓBox12 auteur PASS puis ΓContour FAIL (composition ContinuousAt et API intégrale absente), Mellin et Inversion non invoqués ;2enfants11:26:43–11:27:29UTC. Reçus complets et hashes liés, conservation74/6476 et6524/24captures/3089archives. Jugeψ52 en préparation ; globalH1 numérique et formal, coefficientN,D_N restent ouverts. Officiel63/1057inchangé.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
