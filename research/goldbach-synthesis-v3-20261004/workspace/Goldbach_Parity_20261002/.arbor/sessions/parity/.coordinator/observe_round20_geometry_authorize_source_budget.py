"""Observe actual geometry receipts/bytes and authorize only new SourceBudget."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';G=B/'round20/role4_geometry';W=B/'round20/role4'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
gl=G/'geometry_build_receipt.json'
assert sha(gl)=='dee0fca8a69ce57490d70fd36f9bcab149caad91613655581b807d77cec424de'
ledger=load(gl)
assert [x['exit_code'] for x in ledger['attempts']]==[1,0]
assert [x['credited_pass'] for x in ledger['attempts']]==[False,True]
observed=[]
for x in ledger['attempts']:
    assert x['post_integrity']['all_unchanged'] and not x['post_integrity']['failed_bindings']
    for k in ['source_snapshot','launcher_snapshot','started_receipt','raw_finished_receipt','stdout','stderr','log']:
        assert sha(x[k])==x[k+'_sha256'],k
    start=load(x['started_receipt']);raw=load(x['raw_finished_receipt'])
    assert start['source_sha256']==x['source_sha256']==x['source_snapshot_sha256']
    assert start['command']==x['command'] and raw['exit_code']==x['exit_code']
    for label,check in x['post_integrity']['checks'].items():
        assert check['unchanged'] and check['expected_sha256']==check['actual_sha256']
        if label!='source':assert sha(check['path'])==check['expected_sha256'],label
    observed.append({k:x[k] for k in ['attempt','started_utc','finished_utc','exit_code','credited_pass','source_sha256','log_sha256']})
initial=(G/'attempt01_source_PREEXEC.lean.txt').read_text(encoding='utf-8')
current=(G/'FriableSourceGeometry.lean').read_text(encoding='utf-8')
old='    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)'
new='    calc\n      Real.log (2 : ℝ) ≤ (2 : ℝ) - 1 :=\n        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)\n      _ = 1 := by norm_num'
assert initial.count(old)==1 and initial.replace(old,new)==current
final_path=G/'geometry_final_receipt.json'
assert sha(final_path)=='a82ae5719c1ce90a2969fa286ac32731893f9d606da342a839bec65d57a56c3d'
final=load(final_path)
for rel,digest in final['bindings'].items():assert sha(G/rel)==digest,rel
obs={'round':20,'node':'14.5','at_utc':datetime.now(timezone.utc).isoformat(),
     'actual_geometry_attempts':observed,'ledger_sha256':sha(gl),
     'only_source_repair_exactly_verified':True,'full_initial_source':['92f26e','50be8a','12db54'],
     'full_repair_delta':'9c7671','FULL_actual_logs':['533706','e42edf'],
     'FULL_geometry_FINAL_failures_receipt':'d67d43','final_receipt_sha256':sha(final_path),
     'all_actual_friable_author_attempts_including_geometry':22,'author_pass_count':9,'technical_fail_count':13,
     'root_lean_executions':0,'root_mathematical_executions':0,'victory':False}
obs_path=C/'messages/round20_source_geometry_root_observation.json';save(obs_path,obs)
prep_path=W/'source_budget_preparation.json'
assert sha(prep_path)=='6869878943146995af8b5e7c162be86908f69cefe3bda3d8881f3fb731ffcb31'
p=load(prep_path)
assert p['new_source_budget_Lean_invocations']==0 and p['status']=='SOURCE_BUDGET_PREPARED_NOT_COMPILED'
for name,key in [('build_receipt.json','base_build_receipt_sha256'),('extension_build_receipt.json','extension_build_receipt_sha256'),
                 ('aggregation_build_receipt.json','aggregation_build_receipt_sha256')]:assert sha(W/name)==p[key]
assert sha(gl)==p['geometry_build_receipt_sha256']
assert sha(G/'compile_once.py')==p['geometry_builder_sha256']
for path,digest in p['base_frozen_import_bindings'].items():assert sha(path)==digest,path
assert len(p['base_frozen_import_bindings'])==18
assert sha(W/'build_source_budget.py')==p['builder_sha256']=='0e3c8870eab7ae5859ff8e64a8de1850ec0661cd87aaa10834f7dbf462ef833a'
assert sha(W/'FriableSourceBudget.lean')==p['initial_reviewed_source_sha256']['FriableSourceBudget.lean']=='ab22cac8d3a55eb26322d714579a56e104e6ba4d96770f59b521c4300aa41817'
assert sha(W/'dependencies_readonly.json')==p['historical_dependencies_manifest_sha256']
for rel,digest in load(W/'dependencies_readonly.json')['bindings'].items():assert sha(B/rel)==digest,rel
prior=load(C/'messages/round20_formal4_authorization_phase4.json')
for rel,digest in prior['numeric_bindings'].items():assert sha(B/rel)==digest,rel
assert load(B/prior['numeric_receipt_relative_path'])['exit_code']==0
assert not (W/'source_budget_build_receipt.json').exists()
gate={**{key:p[key] for key in ['base_build_receipt_sha256','extension_build_receipt_sha256','aggregation_build_receipt_sha256',
             'geometry_build_receipt_sha256','geometry_builder_sha256','base_frozen_import_bindings','builder_sha256','initial_reviewed_source_sha256']},
      'authorization':'ROOT20_FORMAL4_SOURCE_BUDGET_COMPILE','root_authorized':True,'round':20,'node':'14.5','phase':6,
      'canonical_new_numeric_pass_inspected':True,'authorized_new_modules':['FriableSourceBudget.lean'],
      'authorized_at_utc':datetime.now(timezone.utc).isoformat(),'preparation_sha256':sha(prep_path),
      'numeric_bindings':prior['numeric_bindings'],'numeric_receipt_relative_path':prior['numeric_receipt_relative_path'],
      'source_geometry_root_observation_sha256':sha(obs_path),'full_source_read':'c4e4a7','full_launcher_read':'b14c3a','full_preparation_read':'9c7671',
      'policy':{'only_new_source_budget_target':True,'changed_FAIL_repairs_only':True,'PASS_replay':False,
                'unchanged_FAIL_replay':False,'historical_targets':False,'post_integrity_and_actual_exit_required':True},
      'F0_minus_F1_nonfriable_reciprocal_paid':False,'whole_ledger_paid':False,
      'root_lean_executions':0,'root_mathematical_executions':0,'victory':False}
out=C/'messages/round20_formal4_authorization_phase6.json';save(out,gate)
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_SOURCE_BUDGET_PHASE6_AUTHORIZED_FORMAL3_SIX_NEW_MODULES_RUNNING'
cp['source_geometry_executor']['status']='FINAL_AUXILIARY_GEOMETRY_PASS_OBSERVED_TWO_REAL_ATTEMPTS'
for item in cp['in_flight_executors']:
    if item['role']==4:item['status']='NINE_FROZEN_AUTHOR_PASSES22_ATTEMPTS_ONLY_NEW_SOURCE_BUDGET_PHASE6_AUTHORIZED'
cp['last_progress']+=' Geometry real[1,0]104postchecks/FINALbindings/delta exact verified, nineauthorPASSes inclgeometry. Budgetsource+lance+prep FULL, phase6onlynewmodule18imports/38numeric bytes; noF0minusF1/nonfriable/fullledger/Win.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate':str(out),'sha256':sha(out),'geometry_observation_sha256':sha(obs_path),
                  'nine_frozen_passes':True,'source_budget_invocations_at_gate':0,'root_math':0,'victory':False}))
