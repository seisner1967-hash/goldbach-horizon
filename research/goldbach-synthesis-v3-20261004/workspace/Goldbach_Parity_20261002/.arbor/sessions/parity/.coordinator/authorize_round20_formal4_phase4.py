"""Metadata-only: observe actual Demand attempts; authorize new all-rank module."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
W=B/'round20/role4'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,ensure_ascii=False,indent=2); f.write('\n')
base_path=W/'build_receipt.json'
assert sha(base_path)=='acfa7776f904f6718de85466f3ca33e4798af51aefb0cb0dd87f5568fe42a1ad'
base=load(base_path)
ext_path=W/'extension_build_receipt.json'
assert sha(ext_path)=='b38b81a05b20d19ca7a73279c8865a86a7fd25032773eaf40fdd7be020156906'
ext=load(ext_path)
assert [x['exit_code'] for x in ext['attempts']]==[1,0]
assert [x['credited_pass'] for x in ext['attempts']]==[False,True]
observed=[]
for x in ext['attempts']:
    assert x['phase']=='FINISHED' and x['post_integrity']['all_unchanged']
    assert not x['post_integrity']['failed_bindings']
    for field in ['snapshot','builder_snapshot','started_receipt','log']:
        assert sha(x[field])==x[field+'_sha256'],field
    started=load(x['started_receipt'])
    assert started['source_sha256']==x['source_sha256']==x['snapshot_sha256']
    assert started['command']==x['command'] and started['started_utc']==x['started_utc']
    if x['olean']: assert sha(x['olean'])==x['olean_sha256']
    for label,check in x['post_integrity']['checks'].items():
        assert check['unchanged'] and check['actual_sha256']==check['expected_sha256']
        if label=='source': continue # failed source intentionally repaired afterwards
        assert sha(check['path'])==check['expected_sha256'],label
    observed.append({k:x[k] for k in ['attempt','started_utc','finished_utc','exit_code','credited_pass','source_sha256','snapshot','snapshot_sha256','log','log_sha256','olean_sha256']})
prep_path=W/'aggregation_preparation.json'
assert sha(prep_path)=='a883e81457692304b3a8b4f034d11026cd08d0d8f7b744f843bd3702c1d75f82'
prep=load(prep_path)
assert prep['new_aggregation_Lean_invocations']==0 and prep['status']=='AGGREGATION_PREPARED_NOT_COMPILED'
assert prep['base_build_receipt_sha256']==sha(base_path)
assert prep['extension_build_receipt_sha256']==sha(ext_path)
bindings={}
for ledger in [base,ext]:
    for module in ledger['successful_modules'].values():
        for k in ['source','olean']:
            assert sha(module[k])==module[k+'_sha256']
            bindings[module[k]]=module[k+'_sha256']
assert bindings==prep['base_frozen_import_bindings'] and len(bindings)==14
builder=W/'build_aggregation.py'
assert sha(builder)==prep['builder_sha256']=='ec9a68b1c22997dd62520cde1a80c8af42f63e7a98716da8fc60361a62336c1e'
source=W/'FriableDemandAggregation.lean'
assert sha(source)==prep['initial_reviewed_source_sha256'][source.name]=='04e45879ffefb5cdcb7f1fc9f1f4e781a4a884d523e8d89669bda29ae86ce56c'
assert sha(W/'build.py')==prep['original_builder_sha256']
assert sha(W/'build_extension.py')==prep['extension_builder_sha256']
deps_path=W/'dependencies_readonly.json'
assert sha(deps_path)==prep['historical_dependencies_manifest_sha256']
deps=load(deps_path)['bindings']
for rel,expected in deps.items(): assert sha(B/rel)==expected,rel
prior_path=C/'messages/round20_formal4_authorization_phase3.json'
assert sha(prior_path)=='fa94239c8bbac3a758382f977a14a05ec1b10e80327f508059b0fbe7e675e219'
prior=load(prior_path)
for rel,expected in prior['numeric_bindings'].items(): assert sha(B/rel)==expected,rel
assert load(B/prior['numeric_receipt_relative_path'])['exit_code']==0
assert not (W/'aggregation_build_receipt.json').exists()
obs={'round':20,'role':4,'at_utc':datetime.now(timezone.utc).isoformat(),
     'extension_ledger_sha256':sha(ext_path),'actual_extension_attempts':observed,
     'all_actual_author_attempts':18,'author_pass_count':7,'technical_fail_count':11,
     'frozen_new_import_bindings':bindings,'numeric_binding_count':len(prior['numeric_bindings']),
     'historical_binding_count':len(deps),'full_current_demand_and_actual_logs':'2ae025',
     'full_aggregation_source':'520796','full_aggregation_launcher':'319d1a','full_preparation':'279546',
     'root_lean_executions':0,'root_mathematical_executions':0,'victory':False}
obs_path=C/'messages/round20_formal4_phase3_root_observation.json'
save(obs_path,obs)
gate={'authorization':'ROOT20_FORMAL4_AGGREGATION_COMPILE','root_authorized':True,
      'canonical_new_numeric_pass_inspected':True,'round':20,'node':'14.5','phase':4,
      'authorized_at_utc':datetime.now(timezone.utc).isoformat(),
      'authorized_new_modules':['FriableDemandAggregation.lean'],
      'builder_sha256':sha(builder),'preparation_sha256':sha(prep_path),
      'initial_reviewed_source_sha256':prep['initial_reviewed_source_sha256'],
      'base_build_receipt_sha256':sha(base_path),'extension_build_receipt_sha256':sha(ext_path),
      'base_frozen_import_bindings':bindings,'numeric_bindings':prior['numeric_bindings'],
      'numeric_receipt_relative_path':prior['numeric_receipt_relative_path'],
      'actual_numeric_exit_code':0,'historical_dependencies_manifest_sha256':sha(deps_path),
      'root_observation_sha256':sha(obs_path),'full_source_read':'520796','full_launcher_read':'319d1a',
      'full_preparation_read':'279546',
      'policy':{'changed_repairs_only_after_actual_failure':True,'PASS_replay':False,
                'unchanged_FAIL_replay':False,'historical_compilations':False,
                'post_integrity_required':True,'other_new_modules_need_separate_FULL_gate':True},
      'root_lean_executions':0,'root_mathematical_executions':0,'victory':False}
gate_path=C/'messages/round20_formal4_authorization_phase4.json'
save(gate_path,gate)
cp_path=C/'checkpoint.json'
cp=load(cp_path)
cp['phase']='ROUND20_ALL_RANK_AGGREGATION_PHASE4_AUTHORIZED_COMPOSITE_V4_AND_GEOMETRY_REVIEW_PENDING'
for item in cp['in_flight_executors']:
    if item['role']==4: item['status']='SEVEN_FROZEN_AUTHOR_PASSES_ONLY_NEW_AGGREGATION_PHASE4_AUTHORIZED'
cp['last_progress']+=' Demand real [1,0], seven frozen PASSes/18 actual attempts verified bytes and START/log/exit; new aggregation only phase4 FULL/gate. No Judge20/sourcebudget/fullledger/Win.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate':str(gate_path),'gate_sha256':sha(gate_path),'observation_sha256':sha(obs_path),
                  'author_passes':7,'actual_attempts':18,'new_module':source.name,'root_math':0,'victory':False}))
