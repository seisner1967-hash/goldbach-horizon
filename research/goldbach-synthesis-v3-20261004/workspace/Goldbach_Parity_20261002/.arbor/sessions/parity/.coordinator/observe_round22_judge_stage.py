"""Reusable ROOT observer for a closed Judge stage; metadata-only aggregation."""
import argparse,hashlib,json,re,subprocess,sys
from datetime import datetime,timezone
from pathlib import Path
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
def sha(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):d.update(block)
 return d.hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
parser=argparse.ArgumentParser()
for name in ['batch','receipt-sha','adjudication-sha','completion-sha','ROOT-full-read-receipts','insight']:
 parser.add_argument('--'+name,required=True)
parser.add_argument('--prior-modules',type=int,required=True)
parser.add_argument('--prior-declarations',type=int,required=True)
args=parser.parse_args();assert re.fullmatch(r'batch[0-9]{2}',args.batch)
P=B/'round22/judge5'/args.batch;A=P/(args.batch+'_attempt01')
for p,digest in [(A/'receipt.json',args.receipt_sha),(P/'adjudication.md',args.adjudication_sha),(P/'completion_receipt.json',args.completion_sha)]:
 assert re.fullmatch('[0-9a-f]{64}',digest) and sha(p)==digest,str(p)
r=read(A/'receipt.json');d=read(P/'completion_receipt.json');pre=read(A/'PREEXEC.json');post=read(A/'POSTEXEC.json');m=read(P/'prepared_manifest.json')
assert r['status']==d['status'] and r['all_inputs_unchanged'] and d['all_current_bytes_preserved']
for flag in ['author_olean_used','hidden_retries','old_batches_recompiled','numeric_bank_replayed','numeric_PASS_used_as_proof','victory','H1_paid','C3_paid','C5_paid','C6_paid','D_N_paid','global_trace_certified']:assert not r[flag],flag
assert pre['inputs']==post['inputs']==m['immutable_inputs']
assert post['all_inputs_unchanged'] and post['gate_unchanged'] and post['captures_unchanged']
assert pre['gate_sha256']==post['gate_sha256']==sha(Path(pre['gate_path']))
for x in pre['inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
for x in pre['captures']:assert sha(Path(x['source']))==sha(Path(x['capture']))==x['sha256']
assert pre['protected_archives']==post['protected_archives'] and len(pre['protected_archives'])==3089
for x in pre['protected_archives']:assert sha(B/x['path'])==x['sha256'],x['path']
old=read(P/'closed_judge_bindings.json')
for x in old['inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
assert [x['module'] for x in r['rows']]==m['modules'][:len(r['rows'])]
assert r['actual_child_invocations']==len(r['rows']) and 0<len(r['rows'])<=len(m['modules'])
passed=[x for x in r['rows'] if x['status']=='INDEPENDENT_LEAN_AUX_PASS']
failed=[x for x in r['rows'] if x['status']=='INDEPENDENT_LEAN_AUDIT_FAIL']
assert len(passed)+len(failed)==len(r['rows']) and len(failed)<=1
assert not failed or r['rows'][-1]==failed[0]
for x in r['rows']:
 assert sha(A/(x['module']+'.log'))==x['log_sha256']
 assert sha(P/'sources'/(x['module']+'.lean'))==x['source_sha256']
 if x in passed:
  assert x['exit_code']==0 and x['exact_axiom_coverage_standard_only']
  assert sha(A/(x['module']+'.olean'))==x['olean_sha256']
 else:assert x['exit_code']!=0 or not x['exact_axiom_coverage_standard_only']
for module in m['modules'][len(r['rows']):]:
 for suffix in ['_START.json','_FIN.json','.log','.olean']:assert not (A/(module+suffix)).exists()
declarations=sum(len(x['axiom_rows']) for x in passed)
assert len(passed)==r['module_count_passed']==d['modules_passed']
assert declarations==r['declarations_passed']==d['declarations_passed']
cp_path=C/'checkpoint.json';cp=read(cp_path);prior=cp['official_auxiliary_validation']
assert prior['modules']==args.prior_modules and prior['declarations']==args.prior_declarations
modules=args.prior_modules+len(passed);total=args.prior_declarations+declarations
o=dict(schema='ROUND22_ROOT_JUDGE_STAGE_CLOSED_OBSERVATION',time_utc=datetime.now(timezone.utc).isoformat(),
 batch=args.batch,status=r['status'],new_modules=len(passed),new_declarations=declarations,
 modules_failed=len(failed),modules_not_invoked=len(m['modules'])-len(r['rows']),
 official_modules=modules,official_declarations=total,includes_definitions=True,
 receipt_sha256=args.receipt_sha,adjudication_sha256=args.adjudication_sha,completion_sha256=args.completion_sha,
 ROOT_FULL_read_receipts=args.ROOT_full_read_receipts,source_math_audit_owner='ROLE5',
 inputs_verified=len(pre['inputs']),old_judge_files_verified=len(old['inputs']),archives_verified=3089,captures_verified=len(pre['captures']),
 large_PRE_POST_scope='every entry parsed and all bytes hash-verified; raw FULL source/import text not claimed',
 ROOT_Lean_invocations=0,ROOT_numeric_invocations=0,H1_paid=False,C5_global_paid=False,D_N_paid=False,WIN=False)
path=C/'messages'/('round22_judge_'+args.batch+'_closed_observation.json')
with path.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command,extra in [('record',['--node-id','15.3','--raw-report',args.insight,'--score','0','--insight',args.insight,'--result','JUDGE_STAGE_AUXILIARY_CLOSED_GLOBAL_TARGET_OPEN','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',args.insight])]:
 result=subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*extra],capture_output=True,text=True,encoding='utf-8');assert result.returncode==0,(result.stdout,result.stderr)
prior.update(modules=modules,declarations=total,new_modules=prior['new_modules']+len(passed),new_declarations=prior['new_declarations']+declarations,basis=str((P/'completion_receipt.json').relative_to(B)))
cp['phase']='ROUND22_'+args.batch.upper()+'_CLOSED_GLOBAL_ANALYTIC_OBLIGATIONS_OPEN'
cp['last_progress']=args.insight;cp['previous_goal_turn_evidence'].append(str(path.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==5:actor['status']=args.batch.upper()+'_CLOSED_NO_RETRY'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\n'+args.insight+'\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
