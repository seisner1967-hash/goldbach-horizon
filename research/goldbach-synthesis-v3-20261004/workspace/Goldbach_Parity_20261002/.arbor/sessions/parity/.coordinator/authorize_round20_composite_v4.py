"""Metadata-only root FULL-source review gate for unique NEW composite attempt."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
W=B/'round20/role6_composite'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8-sig'))
prep_path=W/'preparation.json'
assert sha(prep_path)=='06a746a70fee6f2149819265e9322d3256ea85cfe323bcf7e62c835125b4e5b0'
prep=load(prep_path)
assert prep['preparation_version']==4 and prep['new_composite_bank_executions']==0
assert prep['old_bank_executions']==prep['Lean_executions']==0
assert prep['all_new_sources_unexecuted'] and prep['preparation_is_metadata_only']
expected={
 'composite_checks.py':'51d78a603be32ca7a4fe2a99f23b22871cb21d8cb79ed9b2331d92941f4e2e81',
 'bank.py':'77768ba2d0b97b82b22aca9dc06de9ed7b14691ca2afe05926b5e80e4541dbbd',
 'ap.py':'9bbec647cb84f22e991159eb9143ba518fc5d9efcdccb5deff10ae680d54e82a',
 'reference.py':'43c8c6edeef1bf444adca197bb366a2e0a27be5f3b5f576e43c5454b265b184e',
 'storage.py':'03ab76be3988c5f6ad5d1d3e5423ec45744ab747c5439f87dcc48dfd42b9ba96',
 'integral.py':'512f7f51841720350c407cfc754f4b0e5dad4492abcca4f2b13e745364b9e3f4',
 'certify.py':'4d3a9acf183b86ba67b99e282cc0d3021f6b1fbb916f065a61de3723b5134ef2',
 'arithmetic.py':'131a38a8bf82a46fbc954455d63b6de8ac3055b7b73199b1c555826d04f9cbbc',
 'outward.py':'9823d58d56a8854759cd05268c9fe4fe80b9943b34b190dd129618abbf1b43a8',
 'run_once.py':'2c7a502f123c6b7eab29d311d8cceac0d741a509e8508a65aa8d4cfa0f803230'}
assert prep['code_sha256']==expected
for name,digest in expected.items(): assert sha(W/name)==digest,name
assert len(prep['frozen_input_sha256'])==prep['frozen_input_count']==21
for path,digest in prep['frozen_input_sha256'].items(): assert sha(path)==digest,path
assert sha(prep['runtime'])==prep['runtime_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert prep['preexec_capture_design']['total']==33
assert prep['strict_fixed_sign_design']['unseparated_nonzero_fixed_sign_raises_ArithmeticError']
assert prep['strict_fixed_sign_design']['D_W_evaluations_absent']==0
assert not (W/'canonical_attempt01').exists()
assert not (W/'canonical_attempt01_reserved.json').exists()
assert not (B/'round20/composite.json').exists()
gate={
 'authorization':'ROOT20_COMPOSITE_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01',
 'root_authorized':True,'round':20,'role':6,'node':'13.12','attempt':1,
 'authorized_at_utc':datetime.now(timezone.utc).isoformat(),
 'all_sources_fully_read':True,'canonical_new_numerical_execution_authorized':True,
 'new_bank_only':'COMPOSITE20_13.12','code_sha256':expected,'preparation_sha256':sha(prep_path),
 'preparation_version':4,'frozen_input_sha256':prep['frozen_input_sha256'],
 'full_root_reads':{
   'bank.py':['60aecc:first175','acd8a2:175..399','183f04:400..609','f12d16:610..end'],
   'ap.py':['d0183f'],'reference.py':['54050c:complete-source-before-preparation'],
   'certify.py':['1c92ec'],'composite_checks.py':['1c92ec'],'run_once.py':['5e051d'],
   'preparation.json':['60aecc'],'storage.py':['c753bb'],'integral.py':['7e7343'],
   'arithmetic.py':['ddaf18'],'outward.py':['dc8689']},
 'policy':{'one_canonical_new_execution_only':True,'routine_PASS_replay':False,
           'old_producer_execution':False,'historical_Lean_compilation':False,
           'actual_FIXED_sign_or_exact_ZERO_required':True,
           'nonseparated_FIXED_nonzero_aborts':True,'principal_integral_SN_box_scope_distinct':True,
           'source_onset_or_budget_not_inferred_from_finite_bank':True,
           'all_33_PREEXEC_captures_START_exit_binarylog_and_after_bytes_required':True},
 'root_lean_executions':0,'root_mathematical_executions':0,
 'source_budget_established':False,'victory':False}
out=C/'messages/round20_composite_authorization.json'
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp_path=C/'checkpoint.json'
cp=load(cp_path)
cp['phase']='ROUND20_COMPOSITE_V4_UNIQUE_NEW_ATTEMPT_AUTHORIZED_AGGREGATION_RUNNING_GEOMETRY_PREPARING'
for item in cp['in_flight_executors']:
    if item['role']==6: item['status']='FRIABLE_CLOSED_FINAL_COMPOSITE_V4_FULL_REVIEWED_ONE_NEW_ATTEMPT_AUTHORIZED'
cp['last_progress']+=' Composite stablev4 10code/21input bytes FULL verified; explicit fixed sign abort/exact prime-log ZERO, both local falsifiers true computations in producer. Unique new attempt1 authorized; root no math. AllFINAL20 and Judge20 pending/noWin.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate':str(out),'sha256':sha(out),'code_bindings':len(expected),
                  'frozen_inputs':21,'expected_captures':33,'root_math':0,'victory':False}))
