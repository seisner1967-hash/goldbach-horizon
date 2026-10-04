"""Authorize one frozen independent Gamma numerical producer; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role6/gamma_h2'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
pp=P/'gamma_preparation22.json'; mp=P/'gamma_prepared_manifest22.json'
assert sha(pp)=='c9596f415b725d5db92dbdcd3a5de0bd7b972c35113e2dd16cd7aa87d6b25588'
assert sha(mp)=='4727f3969da2fef60070f1f29bcdbc61c62496db6db7f536c628285e312bcd99'
assert sha(P/'gamma_prepared_receipt22.json')=='2dab809c3ab0689b5ac6a7640a1749a6d892f19ff2e001ff73eabeb2b2fd0e2a'
p=read(pp); m=read(mp); contract=read(P/'gamma_contract22.json')
assert p['status']==m['status']==contract['status']=='PREPARED_SOURCE_ONLY_NOT_EXECUTED'
assert len(p['bindings'])==p['binding_count']==15 and m['binding_count']==14 and p['captures_before_START']==17
assert p['bindings'][:-1]==m['bindings'] and p['Gamma_math_executions']==p['Gamma_Lean_executions']==0 and not p['sole_attempt_consumed']
for row in p['bindings']:
    path=Path(row['path']); assert sha(path)==row['sha256'] and path.stat().st_size==row['bytes'],row['path']
assert contract['canonical_case_count_before_any_mask']==21 and contract['cell_count']==9728 and contract['mutant_case_count']==12
assert contract['expected_exp_calls']==38981 and contract['expected_sin_cos_calls']==68117 and contract['expected_sqrt_certificates']==43
assert not (P/'actual_gamma22').exists()
gp=C/'messages/round22_gamma_numeric_authorization.json'
gate={'schema':'round22.root.gamma_numeric_authorization.v1','created_utc':datetime.now(timezone.utc).isoformat(),'status':'AUTHORIZED','actor':'ROLE6','actor_task':'/root/round21_numeric_conservation','node_id':'15.2','bank_id':p['bank_id'],'scope':p['scope'],'preparation_sha256':sha(pp),'bindings':p['bindings'],'actual_math_invocations_maximum':1,'no_hidden_retry':True,'no_G0_replay':True,'Lean_gate_closed':True,'no_Weil_heat_coefficientN_DN_WIN_credit':True,'canonical_cases':21,'cells_evaluated_each':9728,'expected_mutants_applicable':12,'expected_sqrt_certificates':43,'FULL_root_reads':{'producer_final':'216019','arithmetic_final_unchanged':'eaaeb4','paper_final_unchanged':'3c2f0d','contract_final':'7e19b1','launcher_final_unchanged':'8c1318','metadata_builder':'c531bd','notes':'ab0b9a','manifest':'fb939e','preparation':'e47852','prepared_receipt':'ab6907','read_scope_final':'f471c8','genuine_Gamma_Lean_source':'701280'},'actor_metadata_actual':'f96382 exit0 07:25:30.6440552UTC','root_metadata_IO_incident':'9ee542 tried .py builder; actual builder is .ps1, corrected FULLc531bd, no producer invoked.','proof_scope':'Exact interval elementary primitives plus paper Cauchy and tails; reflection/Laplace analytic obligations explicit, not proved by sampling.'}
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_NUMERIC_ONE_ATTEMPT_AUTHORIZED_FINITE_SOURCE_CORRECTION'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_gamma_numeric_authorization.json','round22/role6/gamma_h2/gamma_preparation22.json','round22/role6/gamma_h2/gamma_contract22.json']
for actor in cp['in_flight_executors']:
    if actor['role']==6: actor['status']='ONE_GAMMA_NUMERIC_ATTEMPT_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'bindings_verified':15,'PREEXEC_copies_expected':17,'scope':p['scope'],'math_invocations_authorized':1,'Lean_authorized':False,'root_math_invocations':0,'WIN':False},ensure_ascii=False,indent=2))
