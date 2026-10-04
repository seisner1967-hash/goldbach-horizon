"""ROOT metadata gate only: hashes, frozen bindings and one author batch."""
import hashlib, json
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role4/h1_contour/analytic_batch01'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'prepared_manifest22.json'; m=read(mp)
assert sha(mp)=='b0cd142deb0198da9e4b17a7cd0298739de3012ff742b1056f9969eef7d6a0a8'
assert sha(P/'run_analytic_batch_once22.py')=='6798b47f5f33934a85da285b033417227be98bbfd8ce23fd6d024b8919e38cea'
assert sha(P/'prepare_analytic_metadata22.ps1')=='b01451b4501e7073bc0dddb957816ba7a2a6649053329edaf9eadc0e665b8a98'
assert sha(P/'read_receipts22.json')=='8ddc1af64bc45c07766289e97a918585f2fce2f7e72260ca4cca47c91f84ace2'
assert sha(P/'preparation22.md')=='a00ff822ecee6c3f1c27608ac3615ebc8e649879569206586dc3593ccc9f89bb'
assert m['schema']=='ROUND22_ROLE4_ANALYTIC_BATCH01_PREPARED'
assert m['status']=='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED'
assert m['declaration_count']==47 and m['compiler_invocations_max']==5
assert m['stop_first_failure'] and m['retry_count']==0
assert m['new_lean_invocations']==m['new_mathematical_python_invocations']==0
assert not any(m[k] for k in ('global_h1_certified','D_N_paid','win','numeric_component_pass'))
assert [r['module'] for r in m['modules']]==['GammaDerivative22','GammaBoxBounds22','GammaContourComponent22','MellinThermal22','MellinThermalInversion22']
assert [r['qualified_print_count'] for r in m['modules']]==[8,12,11,12,4]
assert len(m['immutable_inputs'])==6517
for r in m['immutable_inputs']: assert sha(Path(r['path']))==r['sha256'],r['path']
for r in m['modules']:
    assert sha(Path(r['original_source_path']))==sha(Path(r['staged_source_path']))==r['source_sha256']
    assert len(r['declarations'])==r['qualified_print_count'] and not r['compiled']
assert len(m['import_graph'])==m['import_module_count']==3250
assert not m['unresolved_modules'] and m['implicit_Init_root_bound']
assert any(r['module']=='Init' for r in m['import_graph'])
assert any(r['module']=='Init.Prelude' for r in m['import_graph'])
for r in m['import_graph']:
    assert sha(Path(r['source_path']))==r['source_sha256']
    if r['olean_path']: assert sha(Path(r['olean_path']))==r['olean_sha256']
g=m['gamma_dependency']
assert sha(Path(g['staged_source_path']))==g['source_sha256']=='9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7'
assert sha(Path(g['staged_olean_path']))==g['olean_sha256']=='fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477'
assert sha(Path(g['independent_receipt_path']))==g['independent_receipt_sha256']=='a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9'
assert not g['recompile']
assert m['lean_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
assert m['python_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(Path(m['existing_gamma_bank_path']))==m['existing_gamma_bank_sha256']=='595b15340efe03bd215eebe7f6d526cd1f2f5d07865f074a3b7927687beb967a'
rp=Path(m['component_technical_failure_receipt_path']); r=read(rp)
assert sha(rp)==m['component_technical_failure_receipt_sha256']=='2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48'
assert r['exit_code']==1 and r['result_sha256'] is None and r['post_integrity']
closure=B/'round22/role6/thermal_h1/component_failure_receipt22.json'
assert sha(closure)=='3f4ca3b9c9f03ab4a08c6f4922252a78f91ca768ceeb9aa92f42f1b755eda027'
archives=read(B/'round22/previous_artifacts_sha256.json'); assert archives['file_count']==3089
for rel,expected in archives['sha256'].items(): assert sha(B/rel)==expected,rel
assert not (P/'actual_attempt01').exists()
gate={'schema':'ROUND22_ROLE4_ANALYTIC_BATCH01_AUTHORIZATION_1','created_utc':datetime.now(timezone.utc).isoformat(),
 'authorized':True,'compiler_invocations_max':5,'stop_first_failure':True,'no_retry':True,
 'prepared_manifest_sha256':sha(mp),'existing_gamma_bank_provenance_verified':True,
 'source_bank_scope_compatibility_verified':True,
 'scope_compatibility':'Auxiliary Gamma component only; no global H1 or numerical phase certification',
 'auxiliary_compilation_despite_component_serialization_failure_authorized':True,
 'existing_gamma_bank_sha256':m['existing_gamma_bank_sha256'],
 'component_technical_failure_receipt_sha256':sha(closure),
 'component_failure_technical_serialization_only_verified':True,
 'numeric_PASS':False,'numeric_counterexample_established':False,
 'immutable_inputs_verified':6517,'import_modules_verified':3250,'protected_archives_verified':3089,
 'root_read_scope':'Complete manifest parsed and bytes hashed; import headers only, no FULL cache API claim',
 'root_FULL_reads':{'builder':'1f9059','launcher':'5c4959','preparation':'be004f','read_receipts':'9b8d7e',
 'GammaDerivative':'8e198f','GammaBox':'0183f6','GammaContour_final':'8f41ab','Mellin':'3eb9a0','MellinInversion':'15e2fa'},
 'root_manifest_header_projection':'f6b25c','root_compiler_invocations':0,'root_mathematical_invocations':0,
 'global_H1_paid':False,'D_N_paid':False,'WIN':False}
gp=C/'messages/round22_role4_analytic_batch01_authorization1.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json'; cp=read(cpp)
cp['phase']='ROUND22_PSI_CORE_AUTHOR_FAIL_ANALYTIC_FIVE_AUTHOR_CHILDREN_AUTHORIZED_R01_PREPARED'
for a in cp['in_flight_executors']:
    if a['role']==4:a['status']='ANALYTIC_BATCH01_FIVE_CHILDREN_AUTHORIZED_NOT_STARTED'
    if a['role']==3:a['status']='PSI_CORE_AUTHOR01_TECHNICAL_FAIL_REVISION02_SOURCE'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'inputs_verified':6517,'import_modules_verified':3250,
 'archives_verified':3089,'root_compiler_invocations':0,'root_math_invocations':0,'WIN':False},indent=2))
