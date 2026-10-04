"""Root metadata-only source geometry gate; no compilation or math evaluation."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
W=B/'round20/role4_geometry'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8-sig'))
prep_path=W/'preparation_v2.json'
assert sha(prep_path)=='84b028061f37c88457cf75af185250358c387259f629dcc42361007d2430ee61'
prep=load(prep_path)
assert prep['source_geometry_compiles']==prep['historical_source_compiles']==prep['python_math_runs']==0
assert prep['protocol_version']==2 and prep['complete_post_integrity_required_for_credited_pass']
assert sha(prep['source'])==prep['source_sha256']=='22bb640570931e2d7ad2575347d6b5099270dda4680e3d7472939d4f20449d13'
assert sha(prep['launcher'])==prep['launcher_sha256']=='ac1b9f2e3426a1ca9c311d3d6481b4a102bed6a3ac125ec404f214b47e58baff'
assert sha(prep['report'])==prep['report_sha256']=='e1e952790d256b2724402d3f433bf7591f360d953f135bbeaaa9ed2e38e41e4f'
assert sha(prep['protocol_revision'])==prep['protocol_revision_sha256']=='8467293b40e6075c1412e14c04fcb0cc70f2589cb792911576ee3c5edaac47ec'
assert sha(prep['inputs_manifest'])==prep['inputs_manifest_sha256']=='5d8b757ed6460b34c06ba23014ca95ebf808ee5669a5242e9742823c7e52d997'
manifest=load(prep['inputs_manifest'])
for x in manifest['bindings']: assert sha(x['path'])==x['sha256'],x['path']
for name in ['preparation.json','preparation_v1_NOT_EXECUTED.json']:
    assert sha(W/name)==prep['preserved_v1_preparation_sha256']
assert sha(W/'compile_once_v1_NOT_EXECUTED.py.txt')==prep['preserved_v1_launcher_sha256']
assert sha(prep['compiler'])==prep['compiler_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
assert sha(prep['python_runtime'])==prep['python_runtime_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
prior_path=C/'messages/round20_formal4_authorization_phase4.json'
assert sha(prior_path)=='adf069de88fee864939e6c16be819c5e91b0b6f8ef0f62aa3ec43bb971c002ff'
prior=load(prior_path)
for rel,expected in prior['numeric_bindings'].items(): assert sha(B/rel)==expected,rel
assert load(B/prior['numeric_receipt_relative_path'])['exit_code']==0
assert not (W/'geometry_build_receipt.json').exists()
assert not (W/'FriableSourceGeometry.olean').exists()
gate={'authorization':'ROOT20_GEOMETRY_COMPILE','root_authorized':True,'round':20,'node':'14.5',
      'authorized_at_utc':datetime.now(timezone.utc).isoformat(),
      'authorized_new_modules':['FriableSourceGeometry.lean'],
      'full_geometry_source_read':True,'full_geometry_launcher_read':True,'full_geometry_preparation_read':True,
      'canonical_new_numeric_pass_inspected':True,'allow_repairs_only_after_actual_failed_attempt':True,
      'initial_reviewed_source_sha256':prep['source_sha256'],'launcher_sha256':prep['launcher_sha256'],
      'preparation_sha256':sha(prep_path),'report_sha256':prep['report_sha256'],
      'protocol_revision_sha256':prep['protocol_revision_sha256'],
      'numeric_bindings':prior['numeric_bindings'],'numeric_receipt_relative_path':prior['numeric_receipt_relative_path'],
      'full_root_reads':{'source':['92f26e:first200','50be8a:200..429','12db54:430..end'],
                         'launcher':['d02404'],'preparation_and_protocol':['5e9c85'],
                         'report':['0eea38'],'input_manifest':['0eea38','5ee886:complete-truncated-head']},
      'frozen_input_manifest_sha256':prep['inputs_manifest_sha256'],'input_binding_count':len(manifest['bindings']),
      'policy':{'first_attempt_exact_reviewed_source':True,'changed_FAIL_repairs_only':True,
                'PASS_replay':False,'unchanged_FAIL_replay':False,'historical_targets':False,
                'postbytes_runtime_and_inputs_and_actual_exit_required':True},
      'root_lean_executions':0,'root_mathematical_executions':0,'source_budget_established':False,'victory':False}
out=C/'messages/round20_source_geometry_authorization.json'
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_GEOMETRY_SOURCE_COMPILE_AUTHORIZED_COMPOSITE_REAL_RUN_SOURCE_BUDGET_PREPARING'
cp['source_geometry_executor']={'agent':'/root/round20_ideation_failure_feedback','node':'14.5',
      'status':'NEW_GEOMETRY_MODULE_FULL_READ_DISTINCT_GATE_AUTHORIZED_NO_PASS_YET','gate':str(out),'gate_sha256':sha(out)}
cp['last_progress']+=' Geometry62declarations sourceFULL92f26e/50be8a/12db54, launcher/v2protocolFULLd02404/5e9c85, frozen manifest/38numeric/runtime bytes checked; onlynewGeometry gate. RealchangedFAIL repairs only, root no math; no sourcepayment/Win.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate':str(out),'sha256':sha(out),'input_bindings':len(manifest['bindings']),
                  'numeric_bindings':len(prior['numeric_bindings']),'root_math':0,'victory':False}))
