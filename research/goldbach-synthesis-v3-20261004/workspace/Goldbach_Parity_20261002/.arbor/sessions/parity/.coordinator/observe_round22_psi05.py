"""ROOT records real author Duplication PASS; independent credit remains open."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/role3/h1_psi/revision05/psi_batch05_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'receipt.json')=='74b5dfe2fd4f1b470714fd2d27aee62e678e77ab33f64b36e04eab92fc3ea531'
assert sha(P/'POSTEXEC.json')=='a3c36006a255924ed399e5cd158b617694ac03d416ead234be762ab14e9b76a1'
r=read(P/'receipt.json');p=read(P/'POSTEXEC.json');assert r['status']=='AUTHOR_PSI_BATCH_AUX_PASS' and r['actual_child_invocations']==1 and r['all_inputs_unchanged'] and p['all_inputs_unchanged']
assert len(p['inputs'])==84 and len(p['cache_artifacts_hash_only_readonly'])==6476
for x in p['inputs']+p['cache_artifacts_hash_only_readonly']:assert sha(Path(x['path']))==x['sha256'],x['path']
row=r['rows'][0];assert row['exit_code']==0 and row['exact_axiom_coverage_standard_only'] and len(row['axiom_rows'])==2
assert sha(P/'GammaPsiDuplication22.olean')==row['olean_sha256'] and sha(P/'GammaPsiDuplication22.log')==row['log_sha256']
o={'schema':'ROUND22_PSI05_AUTHOR_PASS_ROOT_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],
 'receipt_sha256':sha(P/'receipt.json'),'ROOT_FULL_read':'9dae70','POST_scope':'Complete JSON parsed/all84inputs6476cachebytes hashed, no FULLraw claim',
 'row':row,'author_PASS_declarations':2,'independent_judge_pending':True,'official_count_delta':0,'root_compiler_invocations':0,'root_numeric_invocations':0,'H1_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_psi05_author_pass_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Psi05 Duplication actual authorPASS2 no sorryAx. Four psi modules all authorPASS19+23+10+2, first52 independent stage gate prepared not yet START because four concurrent slots currently occupied. Numeric globalH1 SOURCE review active; C5/Fubini/Arch/globaltrace/coefficientN/D_N open. Official63/1057 unchanged until independent audit.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','PSI_FAMILY_AUTHOR_PASS_INDEPENDENT_PENDING','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cpp=C/'checkpoint.json';cp=read(cpp);cp['last_progress']=insight
for a in cp['in_flight_executors']:
 if a['role']==3:a['status']='PSI05_CLOSED_DUPLICATION_AUTHOR_PASS_C5_SOURCE_CHECKPOINT'
cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nψ05 : vraie duplication Γ/ψ auteur PASS2, enfantunique11:33:35–11:33:49UTC exit0, deux axiomesstandards, unwarninglinter. Quatre modulesψ désormaisPASSauteur54déclarations ;52enattentedecontrôleindépendantautorisé, Dup2 encoreàauditer séparément. Conservation84/6476. Aucun créditglobalH1/C5/D_N/WIN.\n')
print(json.dumps({k:v for k,v in o.items() if k!='row'},ensure_ascii=False,indent=2))
