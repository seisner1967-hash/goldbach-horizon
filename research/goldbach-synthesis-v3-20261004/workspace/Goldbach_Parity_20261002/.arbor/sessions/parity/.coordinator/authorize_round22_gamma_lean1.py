"""Authorize one frozen Gamma author compilation; metadata and producer statuses only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role4'; A=B/'round22/role6/gamma_h2/actual_gamma22'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'gamma_prepared_manifest3.json'; m=read(mp)
assert sha(mp)=='764c2bd544170e8f232000d690894c79719a8cff27723aa2f9552308daa7f01c'
assert m['status']=='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED' and len(m['immutable_inputs'])==6392 and not m['unresolved_modules']
assert m['compiler_invocations']==m['mathematical_numeric_invocations']==0 and not m['win']
for e in m['immutable_inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert sha(P/'GammaPrerequisites22.lean')==m['source_sha256']=='8bcfef577be2dbf3412646bd7938fe3d929dc0efdd4d1d7c29149ff6102ed7a0'
assert sha(P/'run_gamma_once22_v3.py')==m['launcher_sha256']=='944d9e16ef89bf44fb4f96589dad51c341ce38ec0ccfdb9db30663812c04ebe4'
bank=A/'gamma_result22.json'; r=read(A/'actual_receipt.json'); result=read(bank); obs=read(C/'messages/round22_gamma_pass_observation.json')
assert sha(bank)==r['result_sha256']==obs['hashes']['result']=='595b15340efe03bd215eebe7f6d526cd1f2f5d07865f074a3b7927687beb967a'
assert result['status']==obs['status']=='GAMMA_ROTATED_LAPLACE_AUX_PASS' and r['exit_code']==0 and r['post_integrity']
assert obs['copies_verified']==17 and obs['postbindings_verified']==15 and not obs['WIN']
assert result['cases_evaluated']==21 and result['mutation_detected']==12 and not result['WIN']
assert not (P/'gamma_attempt1').exists()
gate={'schema':'ROUND22_ROLE4_GAMMA_H2_LEAN_AUTHORIZATION_1','created_utc':datetime.now(timezone.utc).isoformat(),'authorized':True,'compiler_invocations':1,'role':4,'node':'15.2','prepared_manifest_sha256':sha(mp),'source_sha256':m['source_sha256'],'launcher_sha256':m['launcher_sha256'],'verified_immutable_inputs':6392,'informative_gamma_bank_path':str(bank),'informative_gamma_bank_sha256':sha(bank),'informative_gamma_bank_verified':True,'informative_gamma_bank_status':result['status'],'numeric_receipt_sha256':sha(A/'actual_receipt.json'),'numeric_observation_sha256':sha(C/'messages/round22_gamma_pass_observation.json'),'root_FULL_reads':{'source':'701280','launcher':'c1ecbe','preparation':'8c1194','metadata_builder':'7a2c6b','read_receipts':'66d2de','manifest_header_only':'e40e82','numeric_receipt':'633b30','numeric_log':'0e7f4b','numeric_case_status_projection':'832bc4'},'manifest_read_scope':'Complete JSON parsed and 6392 input bytes verified; header displayed, not FULL whole text.','root_compiler_invocations':0,'mathematical_numeric_invocations':0,'independent_judge_pending':True,'Weil_certified':False,'zero_count_certified':False,'D_N_paid':False,'WIN':False}
gp=C/'messages/round22_gamma_role4_authorization1.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_FIRST_AUTHOR_COMPILE_AUTHORIZED_UNFOLD_GATE_PENDING'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_gamma_role4_authorization1.json']
for actor in cp['in_flight_executors']:
    if actor['role']==4: actor['status']='GAMMA_H2_ONE_AUTHOR_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':6392,'one_child':'GammaPrerequisites22','independent_judge_pending':True,'root_math_invocations':0,'WIN':False},indent=2))
