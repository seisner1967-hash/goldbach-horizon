"""Issue one role6 numerical authorization after FULL review; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round22'; C=B/'.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
prep_path=R/'role6/epstein_preparation22.json'; manifest_path=R/'role6/prepared_manifest22.json'
assert sha(prep_path)=='78685e62dd2e771ce3c8dde3a89e76817c32479de0ca3e0418ab4fb171134f91'
assert sha(manifest_path)=='178d4aefa216312b1ea7155dd7bee76d3f50e5af508bd2baeded70d8957d22d3'
prep=read(prep_path); manifest=read(manifest_path)
assert prep['binding_count']==len(prep['bindings'])==21
assert manifest['source_count']==len(manifest['bindings'])==20 and prep['bindings'][:-1]==manifest['bindings']
for row in prep['bindings']:
    p=Path(row['path']); assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],str(p)
assert prep['actual_math22']==prep['actual_Lean22']==0
assert prep['N']==100000000 and prep['Y']==10000 and prep['cases']==24
assert prep['scope']=='EPSTEIN_UNFOLDING_AUX_ONLY' and prep['precision_bits']==96
assert prep['tolerance']==[1,100000] and prep['tail_cap']==[1,1000000]
assert not prep['coefficient_N_computed'] and not prep['heat_signal_computed'] and not prep['Weil_trace_computed'] and not prep['D_N_bound_proved'] and not prep['source_onset_satisfied']
assert prep['capture_plan']['planned_total']==23 and prep['one_actual_attempt_only']
assert not Path(prep['reserved_actual_directory']).exists()
tree=read(C/'idea_tree.json'); assert tree['nodes']['16.1']['status']=='running'
selection=read(C/'messages/round22_role2_selection.json'); assert selection['selected_node']=='16.1'
gate_path=C/'messages/round22_epstein_authorization.json'
assert Path(prep['root_authorization_path']).resolve()==gate_path.resolve()
gate={'schema':'round22.root.role6.authorization.v1','status':'AUTHORIZED','actor':'ROLE6','actor_task':'/root/round21_numeric_conservation','created_utc':datetime.now(timezone.utc).isoformat(),'bank_id':prep['bank_id'],'scope':prep['scope'],'selected_node':'16.1','preparation_path':str(prep_path),'preparation_sha256':sha(prep_path),'bindings':prep['bindings'],'allowed_actual_attempts':1,'actual_execution_by_root':False,'execution_state':'AUTHORIZED_NOT_STARTED','immutable_after_gate':True,'root_FULL_reads':{'interval_source':'1d2996','producer':'9990ba','contract':'c7f722','paper':'557988','launcher_final':'934627','metadata_builder':'37ccf1','preparation':'053219','manifest_and_notes_final':'f2179f','ROLE6_report_final':'42d769','readscope':'197601','ROLE2_report':'7bb22f','ROLE2_formula':'9356a6','ROLE2_numeric':'2927c8'},'bounds_scope':'Analytic primitive/tail paper-audited; exact dyadic arithmetic not yet Lean-certified. AUX tests only.','forbidden_credits':['coefficient_N','heat_signal','Weil_trace','D_N_bound','Lean_compile','WIN'],'non_applicable_mutations':'q=1 remains in bank; extra factor2/sign/offby1 mutations not yet claimed checked.','gates_remaining':'Any Lean invocation requires actual informative G0 PASS and separate FULL final source/builder/preparation SHA authorization. Gamma/Weil bank distinct.'}
with gate_path.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_ONE_ROLE6_MATH_ATTEMPT_AUTHORIZED_NOT_STARTED'; cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_epstein_authorization.json','round22/role6/epstein_preparation22.json','round22/role6/prepared_manifest22.json','round22/agent6_precontract.md']
for actor in cp['in_flight_executors']:
    if actor['role']==6: actor['status']='G0_ONE_ATTEMPT_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'AUTHORIZED_NOT_STARTED','path':str(gate_path),'sha256':sha(gate_path),'bindings_verified':21,'scope':prep['scope'],'actual_root_math_invocations':0,'Lean_authorized':False,'win':False},ensure_ascii=False,indent=2))
