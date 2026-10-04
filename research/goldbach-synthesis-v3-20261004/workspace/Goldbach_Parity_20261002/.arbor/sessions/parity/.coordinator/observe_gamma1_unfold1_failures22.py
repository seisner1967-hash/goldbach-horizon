"""Record two genuine author failures and conserved bytes; no proof/math/compiler run."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
    with p.open('x',encoding='utf-8') as f: json.dump(v,f,ensure_ascii=False,indent=2); f.write('\n')
A=B/'round22/role4/gamma_attempt1'; gr=read(A/'receipt.json'); gm=read(B/'round22/role4/gamma_prepared_manifest3.json')
assert gr['exit_code']==1 and gr['compiler_invocations']==1 and gr['olean_sha256'] is None and not gr['changed_immutable_inputs'] and not gr['win']
assert sha(A/'stdout.log')==gr['stdout_sha256']=='3735c5ebe7fbfe53920bc03d47a5d1894422e4aab4557a61576490649911cf0f'
assert sha(A/'stderr.log')==gr['stderr_sha256'] and gr['archive_after']['checked']==3089 and not gr['archive_after']['changed']
assert len(gr['captured_inputs'])==8 and len(gm['immutable_inputs'])==6392
for e in gr['captured_inputs']: assert sha(Path(e['captured']))==e['sha256']==sha(Path(e['original']))
for e in gm['immutable_inputs']: assert sha(Path(e['path']))==e['sha256']
go={'created_utc':datetime.now(timezone.utc).isoformat(),'status':gr['status'],'actual_compiler_invocations':1,'started':gr['start_utc'],'finished':gr['finish_utc'],'exit_code':1,'source_sha256':gr['source_sha256'],'stdout_sha256':gr['stdout_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':8,'inputs_verified':6392,'root_FULL_reads':{'log':'b1f5c1','receipt':'5ad642','START':'a59c59'},'error_lines':[79,132,197,223,241,293],'error_count':6,'classes':['missing cpow continuity API','two redundant tactics after solved goal','commuting exponential argument','positivity on inappropriate target','beta-reduction before norm rewrite'],'sorryAx_recovery_zero_formal_credit':True,'analytic_or_parity_refutation_claim':False,'revision_policy':'Distinct SOURCE ONLY input and root gate required.','WIN':False,'root_compiler_invocations':0}
save(C/'messages/round22_gamma_failure01_observation.json',go)
A=B/'round22/role3/stage03/stage03_attempt01'; r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); row=r['rows'][0]
assert r['actual_child_invocations']==1 and row['exit_code']==1 and row['olean_sha256'] is None and not r['victory']
assert sha(A/'EpsteinUnfold22.log')==row['log_sha256']=='f187b9a31dbfe4c85cb51c6bbfef4ea6a069babd296f582737b66ce50ee50b54'
assert pre['inputs']==post['inputs'] and len(pre['inputs'])==25 and post['unchanged']
copies=sorted((A/'PREEXEC').iterdir()); assert len(copies)==25
for p,e in zip(copies,pre['inputs']): assert sha(p)==e['sha256']==sha(Path(e['path']))
uo={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'started':row['started_at'],'finished':row['finished_at'],'exit_code':1,'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],'receipt_sha256':sha(A/'receipt.json'),'copies_verified':25,'inputs_verified':25,'root_FULL_reads':{'log':'7905ed','receipt':'b887af','START':'c5d400'},'error_lines':[83,153,182],'error_count':3,'classes':['redundant rpow_natCast rewrite','missing square absolute-value normalization','negSucc cast not definitionally equal'],'sorryAx_recovery_zero_formal_credit':True,'infinite_G0_complete':False,'analytic_or_parity_refutation_claim':False,'revision_policy':'Distinct SOURCE ONLY input and root gate required.','WIN':False,'root_compiler_invocations':0}
save(C/'messages/round22_unfold_failure01_observation.json',uo)
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
for node,insight,result in [('15.2','Genuine Gamma bank21cases AUX_PASS remains; first Gamma author compile exit1 six API/tactic errors,8captures/6392inputs and3089archives conserved. Zero olean/formal Gamma credit; separate revisionSOURCE pending. TrueWeil/zeroCount/completezeros/coefficientN/D_N OPEN,noWin.','GAMMA_NUMERIC_AUX_PASS_FIRST_FORMAL_TECHNICAL_FAIL'),('16.1','Kernel/Finite actual author PASS preserved; first infinite Unfold author compile exit1 three rpow/square/cast errors,25captures conserved. Zero olean/infinite G0 credit; separate revisionSOURCE pending. Round22authors2PASS5technicalFAIL. IndependentJudgeSOURCE started; official57/942 unchanged,globalD_N OPEN,noWin.','KERNEL_FINITE_PASS_UNFOLD_FIRST_TECHNICAL_FAIL')]:
    invoke('record','--node-id',node,'--raw-report','# Running '+node+' — actual author failure\n\n'+insight+'\n','--score','0','--insight',insight,'--result',result,'--no-propagate')
    invoke('update','--node-id',node,'--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_UNFOLD_FIRST_TECHNICAL_FAILURES_REVISION_SOURCE_JUDGE_PREP'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_gamma_failure01_observation.json','.arbor/sessions/parity/.coordinator/messages/round22_unfold_failure01_observation.json','round22/role6/gamma_h2/gamma_completion22.md','round22/role6/weil_gamma_interface22.md']
for actor in cp['in_flight_executors']:
    if actor['role']==3: actor['status']='KERNEL_FINITE_PASS_UNFOLD_REVISION02_SOURCE_ONLY'
    if actor['role']==4: actor['status']='GAMMA_FIRST_TECHNICAL_FAIL_REVISION_SOURCE_ONLY'
    if actor['role']==6: actor['status']='G0_GAMMA_TWO_ACTUAL_AUX_PASS_CLOSED_ACTOR_COMPLETE'
cp['in_flight_executors'].append({'role':5,'agent':'/root/round22_judge5_independent','status':'INDEPENDENT_SOURCE_AUDIT_PREPARATION_NO_COMPILER_GATE'})
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nΓ auteur1 : exit1 à07:50:40UTC, six erreurs API/tactiques,8captures/6392inputs inchangés, pas olean. Unfold auteur1 : exit1 à07:51:23UTC, trois erreurs rpow/carré/cast,25captures inchangées, pas olean. Deux révisions SOURCE séparées requises ; aucune réfutation analytique ni victoire. Juge5 prépare indépendamment Kernel/Finite réels PASS. Compteur auteur22 :2PASS/5FAIL techniques, officiel57/942 inchangé.\n')
print(json.dumps({'Gamma_failure':go,'Unfold_failure':uo,'author_PASS':2,'author_FAIL':5,'official_modules':57,'official_auxiliary_statements':942,'WIN':False},ensure_ascii=False,indent=2))
