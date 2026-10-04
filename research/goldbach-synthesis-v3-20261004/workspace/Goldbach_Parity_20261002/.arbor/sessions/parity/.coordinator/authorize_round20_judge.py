"""Issue the reviewed Judge20 gate from byte metadata; never invoke its audit."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';J=B/'round20/judge'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def save(p,data):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
prep_hash='fe440243022cf4111c61827f7b6a387e4a2182cd3523b4aef41ae411abcda6a7'
assert sha(J/'preparation.json')==prep_hash
p=load(J/'preparation.json')
assert p['status']=='READY_AFTER_ALL_FROZEN_FINALS_NOT_EXECUTED'
assert p['all_required_FINALs_frozen'] and p['new_module_count']==16
assert p['actual_independent_Lean_invocations']==p['new_mathematical_python_invocations']==p['numeric_producer_or_sign_replays']==0
assert not p['author20_oleans_in_LEAN_PATH'] and not p['victory']
assert p['static_explicit_declaration_counts_NOT_independent_PASS']=={'def':83,'structure':1,'theorem':250}
assert p['static_axiom_print_count_NOT_independent_PASS']==334
codes={'audit.py':'6ecf1f28163623c7a691341aeb724eba8e3e4265e6555bf359346e84344f8726',
 'run_once.py':'858c657259a4dc844736ffe33e6fd4934168323d1ce64ca8ba08cdd170308299',
 'prepare.py':'3395bc352fc9439f2c086d55f98f2221e9e99326484c46e1dcd22c85be4f31b9'}
assert p['judge_code_sha256']==codes
for name,digest in codes.items():assert sha(J/name)==digest,name
initial=(J/'audit_v01_NOT_EXECUTED.py.txt').read_text(encoding='utf-8')
revised=initial.replace('        assert data["N"] == 100000000',
 '        parameters = data["parameters_and_source_guards"] if bank == "friable" else data["parameters"]\n        assert parameters["N"] == 100000000')
revised=revised.replace('        result[bank] = {"status": data["status"], "N": data["N"],',
 '        guards = parameters["source_guards"] if bank == "friable" else data["source_guards"]\n        result[bank] = {"status": data["status"], "N": parameters["N"],')
revised=revised.replace('                        "stored_source_guards": data.get("source_guards", data.get("source_guard_checks", {})),',
 '                        "stored_source_guards": guards,')
assert revised==(J/'audit.py').read_text(encoding='utf-8')
assert sha(J/'audit_v01_NOT_EXECUTED.py.txt')=='75341d7a4e6c957898c8a69640398f0a2ffb97c04dd2b761ce410f74da197bd6'
assert sha(J/'preparation_v01_NOT_EXECUTED.json')=='14f732ea27cff89d12a12c3ade389ab41eb012426cff408d4d9e204d41c17ab1'
r=load(J/'preparation_metadata_receipt.json')
assert r['preparation_sha256']==prep_hash and r['judge_code_sha256']==codes
assert not r['new_compiler_or_mathematical_execution']
groups={'final_input_sha256':1054,'historical_dependencies_sha256':26,'numeric_frozen_sha256':677,
 'previous_artifacts_sha256':1808,'new_module_sources_sha256':16,'original_documents_sha256':2,'runtime_bindings_sha256':5}
checked={}
for key,count in groups.items():
    assert len(p[key])==count,(key,len(p[key]))
    for path,digest in p[key].items():
        target=Path(path)
        if not target.is_absolute():target=B/target
        assert str(target) not in checked or checked[str(target)]==digest,path
        checked[str(target)]=digest
for path,digest in checked.items():assert sha(path)==digest,path
for key in ['historical_library_dirs','cache_library_dirs']:
    for folder in p[key]:
        target=Path(folder).resolve()
        assert not any(target.is_relative_to((B/'round20'/owner).resolve()) for owner in ['role3','role4','role4_geometry'])
assert len(p['new_module_source_order'])==len(set(p['new_module_source_order']))==16
assert set(p['new_module_source_order'])==set(p['new_module_sources_sha256'])
root_obs=C/'messages/round20_author_finals_root_observation.json'
assert sha(root_obs)=='715e6db355426a2da9f013a6107423886811e03cd815301701d20bbf5bd87ba1'
cross=B/'round20/cross_scope_review'
cross_hashes={'inventory.md':'775b9132cff1c18fd3be9f3c5bbc3b53403f7b8b446e59c66c747616d77a35e0',
 'input_manifest.json':'4aa64966fc559419db43ade6d41e1d5b0a9a32108475a80bdb8f0c7195f7fab2',
 'final_receipt.json':'c8d6bd15b13fbdd7a02e3e19900bc6351247738bdeb38e602fcd5e7a902d9942'}
for name,digest in cross_hashes.items():assert sha(cross/name)==digest,name
for prohibited in ['authorization.json','audit_started.json','input_manifest.json','preexec','audit']:
    assert not (J/prohibited).exists(),prohibited
auth={'authorization':'ROOT20_JUDGE_AUTHORIZED','root_authorized':True,'round':20,'role':5,
 'issued_utc':datetime.now(timezone.utc).isoformat(),'all_required_FINALs_inspected':True,
 'independent_new_module_compile_authorized':True,'canonical_NEW_numeric_results_inspected':True,
 'root_FULL_judge_sources_and_preparation_read':True,
 'root_preparation_read_scope':'All semantic fields and module-plan projection reviewed; every entry of all seven hash dictionaries machine parsed and byte verified. The 565KB opaque digest lists were not claimed individually displayed FULL.',
 'root_source_read_chunks':['84606b (full auditv1 and runv1)','8b8d5f (full prepare and only run integrity-return delta)','7eeb36 (complete unique auditv2 delta)'],
 'root_preparation_semantic_projection_read':'bfd2e6','root_author_finals_observation_sha256':sha(root_obs),
 'preparation_sha256':prep_hash,'judge_code_sha256':codes,'checked_binding_group_counts':groups,
 'unique_byte_bindings_verified':len(checked),'new_modules':16,'canonical_independent_audit_attempt':1,
 'old_producer_Lean_PASS_PDF_sign_or_log_replay_authorized':False,
 'root_execution_scope':'byte/receipt metadata only; ROLE5 owns one actual audit with sixteen fresh Lean invocations',
 'source_onset':'log N>=10^24','source_friable_cost_scope':'theta demand on H19 F0-or-F1 plus unique F1 reciprocal, partial ledger',
 'global_DN_target_proved':False,'victory':False}
save(J/'authorization.json',auth)
obs={'status':'ROUND20_UNIQUE_INDEPENDENT_JUDGE_GATE_ISSUED_ACTUAL_START_PENDING',
 'observed_utc':auth['issued_utc'],'authorization_sha256':sha(J/'authorization.json'),
 'preparation_sha256':prep_hash,'judge_code_sha256':codes,'group_counts':groups,
 'unique_bindings_verified':len(checked),'source_read_scope':auth['root_preparation_read_scope'],
 'static_unexecuted_schema_revision02_not_a_Lean_Judge_failure':True,
 'cross_scope_root_FULL_read':'3b751a','cross_scope_final_hashes':cross_hashes,
 'root_mathematical_compiler_Judge_executions':0,'independent_Judge_started':False,'victory':False}
save(C/'messages/round20_judge_authorization_root_observation.json',obs)
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_INDEPENDENT_JUDGE_AUTHORIZED_ACTUAL_START_PENDING'
for item in cp['in_flight_executors']:
    if item['role']==5:item['status']='UNIQUE_CONCRETE_GATE_ISSUED_ACTUAL_START_PENDING'
cp['last_progress']+=' Judge20FULLcode84606b+8b8d5f+onlyauditdelta7eeb36/prepsemanticbfd2e6 and allopaquehashmaps machinebyteverified; one unique16freshLean gate issued. CrossscopeFULL3b751a found no newcontradiction, actualp0/frame/M0/AP/sourcebridge/debtsopen. SchemaNcorrectionSTATICnotJudgeFAIL. Official41/692 unchanged pendingactualJudge, noWin.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'authorization_sha256':obs['authorization_sha256'],'unique_bindings_verified':len(checked),'root_math':0,'Judge_started':False,'victory':False}))
