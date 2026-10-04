"""Observe finite bank bytes/stored labels and open only six new formal sources."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
V=B/'round20/role6_composite/canonical_attempt01'
W=B/'round20/role3'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
receipt_path=V/'receipt.json'
assert sha(receipt_path)=='523726485fb1ae940dada0673d8226ec2475f43c1a2a9b1e25ac67fe986ebdef'
r=load(receipt_path)
assert r['exit_code']==0 and r['launch_error'] is None and r['after_preservation_pass']
assert r['canonical_subprocess_count']==1 and r['routine_replays']==0
assert r['frozen_input_changes_after']==[]
assert r['runtime_sha256_after']==r['runtime_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(r['runtime'])==r['runtime_sha256']
assert sha(V/'started.json')==r['started_sha256']=='3ae2b682a614932736f3713564b43d4bc729a2f0f9315084e7a889d9d8955e28'
assert sha(r['input_manifest_path'])==r['input_manifest_sha256']=='9a773ec339fba5499e4c5e58757b5f98c15bcd3dd2af7fb40facacdc07a99047'
assert sha(r['log_path'])==r['log_sha256']=='f1f8d5b05f249a0b36bdfc52afc26b10fdfc0f1aca65ba1033fa5603ee0c1bea'
assert sha(r['result_path'])==r['result_sha256']=='f8c8e4806464d1a0267ad5fbf004c7a493e526cc71b94a2a4823a762a9d4034a'
manifest=load(r['input_manifest_path'])
assert len(manifest['bindings'])==33 and manifest['bindings']==r['captures_preexec']
bindings={}
def bind(p,expected):
    p=Path(p).resolve()
    assert p.is_relative_to(B)
    assert sha(p)==expected,str(p)
    rel=p.relative_to(B).as_posix()
    assert rel.startswith('round20/')
    if rel in bindings:assert bindings[rel]==expected
    bindings[rel]=expected
for x in manifest['bindings'].values():
    assert sha(x['original'])==x['sha256']
    bind(x['snapshot'],x['sha256'])
for p,digest in [(receipt_path,sha(receipt_path)),(V/'started.json',r['started_sha256']),
                 (Path(r['input_manifest_path']),r['input_manifest_sha256']),
                 (Path(r['log_path']),r['log_sha256']),(Path(r['result_path']),r['result_sha256'])]:bind(p,digest)
prep_path=B/'round20/role6_composite/preparation.json'
assert sha(prep_path)=='06a746a70fee6f2149819265e9322d3256ea85cfe323bcf7e62c835125b4e5b0'
prep=load(prep_path);bind(prep_path,sha(prep_path))
for name,digest in prep['code_sha256'].items():bind(prep_path.parent/name,digest)
d=load(r['result_path'])
assert d['status']=='PASS_NEW_COMPOSITE20_FINITE_IDENTITIES_SOURCE_GUARDS_FALSE'
assert d['round']==20 and d['node']=='13.12' and not d['victory']
assert d['float_operations']==d['actual_fixed_unresolved_signs']==d['old_producer_or_Lean_executions']==0
assert not d['source_budget_or_Lean_B6_SD_proved']
assert not d['source_guards']['u_ge10pow24'] and not d['source_guards']['x_test_le_Nover4']
for row in d['all_positions_and_certificates_stored_in_catalogs'].values():bind(row['path'],row['sha256'])
for key in ['primitive_logs','complete_bitmap','new_small_prime_axes']:bind(d[key]['path'],d[key]['sha256'])
for row in d['all_reference_fibres_summary']:bind(row['all_b_bitmap']['path'],row['all_b_bitmap']['sha256'])
stored_labels={cfg:{name:value['whole_box_certificate']['sign'] for name,value in entries.items()
                     if 'whole_box_certificate' in value}
               for cfg,entries in d['aggregate_affine_expressions_and_certificates'].items()}
obs={'round':20,'role':6,'node':'13.12','at_utc':datetime.now(timezone.utc).isoformat(),
     'actual_start':r['started_at_utc'],'actual_finish':r['finished_at_utc'],'actual_exit_code':0,
     'receipt_sha256':sha(receipt_path),'result_sha256':r['result_sha256'],'log_sha256':r['log_sha256'],
     'all_33_captures_original_and_snapshot_bytes_verified':True,'canonical_subprocess_count':1,'routine_replays':0,
     'new_numeric_bindings':bindings,'stored_counts':d['counts'],
     'stored_fixed_certificate_labels':d['actual_fixed_sign_certificate_counts'],
     'stored_aggregate_labels':stored_labels,'stored_source_guards':d['source_guards'],'stored_unpaid':d['unpaid'],
     'root_read_actual_receipt_projection_and_result_metadata':'29a7ab',
     'root_numeric_or_factor_log_sign_recomputation':0,'root_lean_executions':0,'victory':False}
obs_path=C/'messages/round20_composite_finish_root_observation.json';save(obs_path,obs)
formal_prep=W/'preparation.json'
assert sha(formal_prep)=='37c3275b9daff66e8734905be5f6f983ed610ad6f3a51d62e12835a1af87c72e'
fp=load(formal_prep)
for rel,digest in fp['historical_dependencies_sha256'].items():assert sha(B/rel)==digest,rel
assert sha(W/'build_once.py')=='323fbb9474088a8b09d909815653cfc3137b8c5623c2f5fb94556cbb0433c7d3'
sources={
 'OddBonferroniArithmetic':'d73a95a78912678878e379b73c60553946b705a1d74c5b37b7ba86d2678c1921',
 'LeastFactorComposite':'a5a64f2b934dab494d8b535fdbd648c9db929dfb9fbe1570c4fb205b9b66332a',
 'SwitchedSelbergWeight':'8d99ee865c4d94e12583be1ceba43b13b9693ea35240e6d4c28195e2fc28fc21',
 'PhysicalCompositeSubtraction':'195d5bae746da74f157e03ffbac109f818f21963776fc50a2776040f05381370',
 'CompositeAPConductor':'aad40a8bef72bcd6eac733302f643634f337cc2aa7cc6824548ed544bdda2c48',
 'SwitchedIncidenceEstimator':'7ae215c13c6f8ae5feb3a4b6628025070afe94c9b717d2de779c39d083538c7b'}
initial={}
for module,digest in sources.items():
    p=W/(module+'.lean');assert sha(p)==digest,module
    initial[p.relative_to(B).as_posix()]=digest
assert not (W/'build_receipt.json').exists()
gate={'compile_authorization_token':'ROOT20_FORMAL3_COMPILE','node_id':'13.12','round':20,
      'formal3_candidate_compilation_authorized':True,
      'root_full_read_current_formal3_sources_and_launcher_confirmed':True,
      'canonical_numeric_pass':True,'actual_identity_false':False,'actual_numeric_exit_code':0,
      'authorized_at_utc':datetime.now(timezone.utc).isoformat(),'authorized_new_modules':list(sources),
      'checked_inputs_sha256':bindings,'initial_sources_sha256':initial,
      'launcher_sha256':sha(W/'build_once.py'),'preparation_sha256':sha(formal_prep),
      'allow_source_changed_repairs_after_actual_failure':True,
      'numeric_finish_root_observation_sha256':sha(obs_path),
      'current_full_source_reads':['92ffce','9c74aa','164dad','82952e','f6899b','00230b'],
      'full_current_launcher_and_preparation_reads':['46a8a7','abb4d2'],
      'policy':{'historical_targets':False,'PASS_replay':False,'unchanged_FAIL_replay':False,
                'all_START_snapshot_exit_log_postbytes_required':True,
                'finite_principal_POS_not_whole_Gamma_or_source_payment':True},
      'root_lean_executions':0,'root_mathematical_executions':0,'victory':False}
out=C/'messages/round20_formal3_compile_authorization.json';save(out,gate)
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_COMPOSITE_CANONICAL_PASS_SIX_FORMAL3_MODULES_AUTHORIZED_SOURCE_BUDGET_PENDING'
for x in cp['in_flight_executors']:
    if x['role']==6:x['status']='TWO_CANONICAL_BANKS_REAL_EXIT0_SOURCE_GUARDS_FALSE_FINAL6_PENDING'
    if x['role']==3:x['status']='SIX_FULL_SOURCES_NEW_COMPOSITE_PASS_CONCRETE_COMPILE_GATE_AUTHORIZED'
cp['last_progress']+=' Composite uniqueFIN04:02:51Z exit0, allcanonicalcatalog/input bytes verified, fixed signs stored separated, actualGamma0_NEG5/principalPOS5 read withoutrecompute. SixnewFormal3 compilegate created, changedFAILrepairsonly. Sourcebudget/Judge20/fullledger/noWin remain.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'numeric_observation_sha256':sha(obs_path),'new_numeric_bindings':len(bindings),
                  'gate':str(out),'gate_sha256':sha(out),'six_new_modules':list(sources),'root_math':0,'victory':False}))
