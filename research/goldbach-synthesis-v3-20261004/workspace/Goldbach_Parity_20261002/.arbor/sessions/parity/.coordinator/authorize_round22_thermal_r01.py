"""ROOT metadata only: authorize one frozen revised component bank."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role6/thermal_h1/revision01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pp=P/'preparation_r01.json';mp=P/'prepared_manifest_r01.json'
assert sha(pp)=='13774751f2ff3f009b1e27d8e8d7b567cc8c216687117f8cf8b163bc7668b555'
assert sha(mp)=='b7219b88f0d1dcf0840133324aa00c63aacdcc03291643f3ee3e2f130ff2a9bb'
p=read(pp);m=read(mp)
assert p['binding_count']==len(p['bindings'])==33 and p['captures_before_START']==35
assert m['binding_count']==len(m['bindings'])==32 and p['bindings'][:-1]==m['bindings']
assert p['status']==m['status']=='PREPARED_SOURCE_ONLY_NOT_EXECUTED'
assert p['actor']==m['actor']=='ROLE6'
assert p['bank_id']==m['bank_id']=='THERMAL_COMPONENT_R01_AUX22'
assert p['scope']==m['scope']=='THERMAL_COMPONENT_R01_AUX_ONLY'
assert p['math_invocations']==p['Lean_invocations']==p['old_producer_invocations']==0
assert not any(p[k] for k in ('sole_attempt_consumed','old_partial_values_as_oracle','cost_measured','runtime_integer_string_limit_modified','H1_claim','WIN'))
assert m['original25bindings_verified'] and m['original_attempt_closed']
assert p['expected_case_count']==46 and p['expected_mutation_count']==19
assert p['expected_Gamma_phase_cases']==15 and p['expected_sqrt_certificates']==15
assert p['expected_reference_cells_each']==2240 and p['expected_reference_cells_total']==33600
assert p['expected_regression_exponents']==[512,768]
assert p['runtime_flags']==['-B','-X','utf8']
for r in p['bindings']:
    q=Path(r['path']);assert sha(q)==r['sha256'] and q.stat().st_size==r['bytes'],r['path']
assert sha(Path(p['runtime_path']))=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
orig=P.parent/'component_preparation22.json'
assert sha(orig)=='b417be88862b3adb9636d90214243c943c4d8e054856dff3e93baf9be1280a5e'
o=read(orig);assert len(o['bindings'])==25
for r in o['bindings']:
    q=Path(r['path']);assert sha(q)==r['sha256'] and q.stat().st_size==r['bytes'],r['path']
failed=P.parent/'actual_component22/actual_receipt.json'
assert sha(failed)=='2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48'
assert read(failed)['exit_code']==1 and read(failed)['result_sha256'] is None
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,expected in archives['sha256'].items():assert sha(B/rel)==expected,rel
assert not Path(p['future_actual_directory']).exists()
gp=C/'messages/round22_thermal_component_r01_authorization.json'
assert Path(p['root_gate_path']).resolve()==gp.resolve()
gate={'schema':'ROUND22_THERMAL_COMPONENT_R01_AUTHORIZATION','created_utc':datetime.now(timezone.utc).isoformat(),
 'status':'AUTHORIZED','actor':'ROLE6','bank_id':p['bank_id'],'scope':p['scope'],
 'preparation_sha256':sha(pp),'prepared_manifest_sha256':sha(mp),'bindings':p['bindings'],
 'sole_mathematical_child':'producer_r01.py','mathematical_invocations_maximum':1,'retry_count':0,
 'old_producer_reexecution_authorized':False,'old_output_or_partial_memory_oracle_authorized':False,
 'original25bindings_verified':True,'protected_archives_verified':3089,'copies_before_START':35,
 'root_FULL_reads':{'preparation':'b1e903','kernel':'f633ac','producer':'a3fcc0','checker':'2f583c',
 'paper':'dbd7e1','launcher':'598909','builder':'f656d0','analytic':'121f25','dyadic':'11d2a7',
 'reference':'9d385f','contract_and_scope':'ad1603'},
 'root_manifest_scope':'Complete JSON parsed and all32bindings verified; header projection a6bb75; no FULL raw manifest claim',
 'mathematical_source_review_owners':'ROLE6 author; ROLE4 paper/kernel/reference FULL b89dfc/d12223, dyadic signatures TARGETED only',
 'root_mathematical_invocations':0,'root_Lean_invocations':0,'global_H1_claim':False,
 'coefficient_N_claim':False,'D_N_claim':False,'WIN':False}
with gp.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json';cp=read(cpp)
cp['phase']='ROUND22_ANALYTIC_AUTHOR_BATCH01_AUTHORIZED_NUMERIC_COMPONENT_R01_AUTHORIZED_PSI_REVISION02_SOURCE'
for a in cp['in_flight_executors']:
    if a['role']==6:a['status']='THERMAL_COMPONENT_R01_ONE_NEW_CHILD_AUTHORIZED_NOT_STARTED'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'new_bindings_verified':33,
 'original_bindings_verified':25,'archives_verified':3089,'root_math_invocations':0,'WIN':False},indent=2))
