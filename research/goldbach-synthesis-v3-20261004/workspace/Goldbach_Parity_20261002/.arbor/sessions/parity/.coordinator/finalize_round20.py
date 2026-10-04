"""Close the already actual FINAL20 using bytes/receipts only; no math or audit replay."""
import json, hashlib, os, re
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round20'; J=R/'judge'; C=B/'.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
def verify(bindings):
    for path,digest in bindings.items(): assert sha(B/path)==digest,path
f=read(J/'final_receipt.json'); m=read(J/'final_manifest.json'); a=read(J/'audit_receipt.json')
d=read(R/'adjudication.json'); i=read(J/'input_manifest.json'); launch=read(J/'launch_receipt.json')
obs=read(C/'messages/round20_judge_finish_root_observation.json')
assert sha(J/'final_receipt.json')=='d9c4055fc98c10628fd7454c38e4d5b3f6d22e8ea994f50b4a7e5fd20e7f8e58'
assert sha(J/'final_manifest.json')==f['final_manifest_sha256']=='3363a833aa5eb8d1e698e3236765d45e156327f0329bc5d32db98b77c4988c5c'
assert sha(R/'agent5_judge.md')==f['report_sha256']==d['report_sha256']=='fb4abdd6cb56bcbf6d8fb85abb9f4990119f3ca495faeefd6cc077c0df95e672'
assert sha(R/'adjudication.json')==f['adjudication_sha256']=='fcc74721566fe8b373c67b6ac113c3ddf5d9aba0168ceee60fc40e7e2190cd87'
assert sha(J/'audit_receipt.json')==f['audit_receipt_sha256']==obs['audit_receipt_sha256']==launch['audit_receipt_sha256']
assert sha(J/'launch_receipt.json')==f['launch_receipt_sha256']==obs['launch_receipt_sha256']
assert sha(J/'input_manifest.json')==a['input_manifest_sha256']==launch['input_manifest_sha256']
assert f['status']=='FINAL5_ACTUAL_INDEPENDENT_LEAN_AUXILIARY_NO_WIN'
assert f['source_and_outputs_frozen'] and f['all_axioms_standard'] and not f['new_math_during_finalization']
assert launch['actual_exit_code']==0 and launch['launch_error'] is None
assert launch['started_utc']==obs['actual_start'] and launch['finished_utc']==obs['actual_finish']
assert len(m['bindings'])==f['manifest_binding_count']==m['binding_count']==189
verify(m['bindings'])
assert f['new_counts']==a['new_counts']==d['new_counts']==obs['new_counts']=={'modules':16,'theorems':250,'defs':83,'structures':1,'axiom_prints':334}
assert f['cumulative_counts']==a['cumulative_counts']==d['cumulative_counts']=={'modules':57,'theorems':942}
assert f['actual_judge_Lean_invocations']==d['actual_new_Lean_invocations']==16
assert f['actual_judge_FAIL']==d['actual_judge_FAIL']==0 and d['actual_unique_judge_launcher_invocations']==1
assert f['actual_author_totals']==d['actual_author_totals']==obs['actual_author_totals']=={'actual_invocations':38,'actual_PASS':16,'actual_FAIL':22}
assert len(obs['independent_module_receipt_observations'])==16
assert all(row['actual_exit_code']==0 for row in obs['independent_module_receipt_observations'])
assert len(obs['style_warnings'])==13
assert not f['victory'] and not d['victory'] and not d['parity_bypass_proved'] and not d['full_fixed_D_N_ledger_paid'] and not d['whole_D_N_target_proved']
assert d['source_friable_cost_bound_proved'] and not d['author20_oleans_imported'] and d['numeric_math_replays']==0
groups=('final_input_sha256','historical_dependencies_sha256','numeric_frozen_sha256','previous_artifacts_sha256','new_module_sources_sha256','original_documents_sha256','runtime_bindings_sha256')
union={}
for group in groups:
    verify(i[group])
    for path,digest in i[group].items():
        resolved=str((B/path).resolve())
        assert resolved not in union or union[resolved]==digest,path
        union[resolved]=digest
assert len(union)==f['checked_input_path_count']==m['checked_input_path_count']==2837
registry=read(R/'previous_artifacts_sha256.json')
assert registry['file_count']==len(registry['sha256'])==1808
assert registry['sha256']==i['previous_artifacts_sha256']
skip={'.git','.lake','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}
old=set()
for folder,dirs,files in os.walk(B):
    dirs[:]=[x for x in dirs if x not in skip and not(re.fullmatch(r'round\d+',x) and int(x[5:])>=20)]
    for name in files:
        p=Path(folder)/name
        if p!=B/'REPORT.md': old.add(p.relative_to(B).as_posix())
assert old==set(registry['sha256']),{'missing':sorted(set(registry['sha256'])-old),'extra':sorted(old-set(registry['sha256']))}
expected={p for p in i['final_input_sha256'] if p.startswith('round20/')}|set(m['bindings'])|{'round20/judge/final_receipt.json','round20/judge/final_manifest.json'}
extras={
 'round20/agent4_geometry_preparation.md','round20/cross_scope_review/final_receipt.json',
 'round20/cross_scope_review/finalize_metadata.ps1','round20/cross_scope_review/input_manifest.json',
 'round20/cross_scope_review/inventory.md','round20/ideation_failure_feedback01.md',
 'round20/ideation_failure_feedback02.md','round20/ideation_failure_feedback03.md',
 'round20/role4_geometry/attempt01.stderr.txt','round20/role4_geometry/attempt01.stdout.txt',
 'round20/role4_geometry/attempt01_launcher_PREEXEC.py.txt','round20/role4_geometry/attempt02.olean',
 'round20/role4_geometry/compile_once_v1_NOT_EXECUTED.py.txt','round20/role4_geometry/preparation_v1_NOT_EXECUTED.json'}
actual={p.relative_to(B).as_posix():sha(p) for p in sorted(R.rglob('*')) if p.is_file() and p.name!='controller_manifest.json'}
assert len(expected)==1205 and len(actual)==1219
assert set(actual)==expected|extras,{'missing':sorted(expected|extras-set(actual)),'extra':sorted(set(actual)-expected-extras)}
for rel,digest in {
 'round20/cross_scope_review/inventory.md':'775b9132cff1c18fd3be9f3c5bbc3b53403f7b8b446e59c66c747616d77a35e0',
 'round20/cross_scope_review/final_receipt.json':'c8d6bd15b13fbdd7a02e3e19900bc6351247738bdeb38e602fcd5e7a902d9942',
 'round20/cross_scope_review/input_manifest.json':'4aa64966fc559419db43ade6d41e1d5b0a9a32108475a80bdb8f0c7195f7fab2',
 'round20/cross_scope_review/finalize_metadata.ps1':'ea23c6967cfb8d61724fed1bb61ea87f707aea383df28320dce59ba8e92df344',
 'round20/ideation_failure_feedback01.md':'562783b7999486ee57fcb66743c08cd52017c3694bca75a45c61198ec9be7d5f',
 'round20/ideation_failure_feedback02.md':'6063a7f05091c3b2ae641d9a984aaa27194aa0b9dc765ca44aaf66e79a5f852b',
 'round20/ideation_failure_feedback03.md':'c478b588394a15d6d6728c82cca02b8488d51fa5775c6d1b949e819a9e093923',
 'round20/agent4_geometry_preparation.md':'e1e952790d256b2724402d3f433bf7591f360d953f135bbeaaa9ed2e38e41e4f'
}.items(): assert actual[rel]==digest,rel
cross=read(R/'cross_scope_review/input_manifest.json')
for entry in cross['entries']: assert sha(B/entry['path'])==entry['sha256'],entry['path']
result={'round':20,'status':'FINAL20_INDEPENDENT_AUXILIARY_AND_PARTIAL_FRIABLE_COST_NO_PARITY_WIN',
 'recorded_utc':datetime.now(timezone.utc).isoformat(),'research_goal_active':True,'objective_complete':False,'score':0,'victory':False,
 'new_counts':f['new_counts'],'cumulative_counts':f['cumulative_counts'],'previous_artifacts_preserved':1808,
 'all_unique_judge_input_paths_verified':2837,'Judge_owned_bindings_verified':189,
 'independent_audit_invocations':1,'independent_audit_exit_codes':[0],'independent_Lean_invocations':16,'independent_Lean_failures':0,
 'independent_style_warnings':13,'producer_Lean_invocations':38,'producer_Lean_failures':22,
 'separate_non_Lean_incidents':['CP1252 display wrapper after saved FAIL01','unexecuted numeric-schema audit revision','unexecuted geometry launcher/preparation revision'],
 'new_numeric_canonical_invocations':2,'numeric_canonical_exit_codes':[0,0],'numeric_replays':0,
 'root_audit_compiler_numeric_or_logarithmic_sign_invocations':0,'source_A7_and_fixed_acquis_unchanged':True,
 'source_onset':'log N >=10^24','source_friable_exceptional_cost_bound':'N/(8192 logN loglogN)',
 'source_friable_cost_bound_proved':True,'F0_minus_F1_nonfriable_reciprocal_paid':False,'full_fixed_D_N_ledger_paid':False,
 'parity_bypass_certified':False,'retained_ledger':'D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0)',
 'semantic_obligations':d['semantic_obligations'],'judge_report_sha256':f['report_sha256'],
 'judge_final_receipt_sha256':sha(J/'final_receipt.json'),'judge_manifest_sha256':sha(J/'final_manifest.json'),
 'adjudication_sha256':sha(R/'adjudication.json'),'audit_receipt_sha256':sha(J/'audit_receipt.json'),
 'original_sources_sha256':i['original_documents_sha256'],'bindings_sha256':actual,
 'preserved_known_auxiliary_extras_sha256':{x:actual[x] for x in sorted(extras)},
 'files_bound':1219,'files_with_self':1220,'next_protected_artifacts_expected':3028,
 'root_full_FINAL_report_read':'3deaff','root_full_FINAL_receipt_read':'4aec30',
 'hash_dictionary_display_scope':'Opaque huge dictionaries parsed and every binding byte-verified; no claim of full textual display.',
 'cross_scope_review_read_only_and_not_new_Judge_PASS':True}
dest=R/'controller_manifest.json'
with dest.open('x',encoding='utf-8') as out: out.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','files_bound','files_with_self','next_protected_artifacts_expected','new_counts','cumulative_counts','victory')}|{'controller_sha256':sha(dest)},ensure_ascii=False,indent=2))
