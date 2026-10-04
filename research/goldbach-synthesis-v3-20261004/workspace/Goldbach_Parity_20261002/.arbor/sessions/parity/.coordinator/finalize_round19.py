"""Close the actual FINAL19 via frozen hashes and receipts, no math or audit replay."""
import sys, json, hashlib, os, re
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round19'; J=R/'judge'; C=B/'.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
def verify(bindings):
    for rel,digest in bindings.items(): assert sha(B/rel)==digest,rel
f=read(J/'final_receipt.json'); m=read(J/'manifest.json'); c=read(J/'closure.json'); outer=read(J/'finalize_metadata_process_receipt.json')
assert sha(R/'agent5.md')==sha(J/'report.md')==f['report_sha256']=='3d21347202a21fe8f8e9f411b40a1045c718ee064b1e612abcaaa92823e4865a'
assert sha(J/'final_receipt.json')==outer['final_receipt_sha256']=='88f1cd3329a15440b14d928faf3b8adad24f35941f6550204fcd98b90e05cce6'
assert sha(J/'manifest.json')==f['manifest_sha256']=='e957beae506a465245cc1d309ed6bd66f01f8ff440a6e8cf6ea3c85cd04004bc'
assert sha(J/'closure.json')==f['closure_sha256']=='de42e259a3573c98157c7e35aa7c11a21c9de067e22e49cff6cd8506e66871fb'
assert f['status']=='FINAL_FROZEN_INDEPENDENT_AUXILIARIES_PASS_NO_WIN' and c['status']=='FINAL5_CLOSED_INDEPENDENT_AUXILIARIES_PASS_NO_WIN'
assert outer['exit_code']==0 and outer['new_Lean_audit_numeric_or_sign_invocations']==0
assert sha(J/'finalize_metadata_process.log')==outer['log_sha256']
assert sha(J/'finalize_metadata.py')==sha(J/'finalize_metadata_source_PREEXEC.py.txt')==outer['source_sha256']==f['metadata_finalizer_source_sha256']
assert f['bindings']==m['bindings'] and len(m['bindings'])==f['binding_count']==145
verify(m['bindings'])
assert f['self_reference_exclusions']==m['self_reference_exclusions']==['final_receipt.json','finalize_metadata_process.log','finalize_metadata_process_receipt.json','manifest.json']
owned={p.relative_to(B).as_posix() for p in J.rglob('*') if p.is_file() and p.name not in f['self_reference_exclusions']}
owned.add('round19/agent5.md'); assert owned==set(m['bindings'])
a=read(J/'audit_receipt.json'); inputs=read(J/'input_manifest.json'); summary=read(J/'audit_summary.json')
obs=read(C/'messages/round19_judge_finish_root_observation.json')
assert obs['status']=='ROOT_VERIFIED_ACTUAL_JUDGE19_AUDIT_EXIT0_FULL_FINAL_CLOSURE_PENDING'
assert sha(J/'audit_receipt.json')==f['audit_receipt_sha256']==obs['audit_receipt_sha256']==summary['audit_receipt_sha256']
assert sha(J/'audit_summary.json')==f['audit_summary_sha256']=='7b8081072073d9b14f7f9696596fba09a83383c8d8ac1a6c6234d47360cd3de9'
assert summary['new_counts']==f['new_counts']==c['new_counts']==a['new_counts']==obs['new_counts']
assert c['candidate_cumulative_counts_for_root_closure']==a['cumulative_counts']=={'modules':41,'theorems':692}
assert c['independent_Lean_invocations']==f['independent_Lean_invocations']==11
assert c['independent_Lean_FAIL']==f['independent_Lean_FAIL']==0
assert c['PASS_replays']==f['PASS_replays']==0 and c['canonical_attempts']==1
assert len(summary['modules'])==11
for row,original in zip(summary['modules'],a['independent_Lean']['modules']):
    for key,value in row.items(): assert original[key]==value,(original['module'],key)
verify(inputs['final_input_sha256']); verify(inputs['historical_dependencies_sha256'])
registry=read(R/'previous_artifacts_sha256.json'); assert len(registry['sha256'])==registry['file_count']==1361
verify(registry['sha256'])
for path,digest in inputs['original_documents_sha256'].items(): assert sha(Path(path))==digest
skip={'.git','.lake','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}
old=set()
for folder,dirs,files in os.walk(B):
    dirs[:]=[d for d in dirs if d not in skip and not(re.fullmatch(r'round\d+',d) and int(d[5:])>=19)]
    for name in files:
        p=Path(folder)/name
        if p!=B/'REPORT.md': old.add(p.relative_to(B).as_posix())
assert old==set(registry['sha256'])
expected={rel for rel in inputs['final_input_sha256'] if rel.startswith('round19/')}|set(m['bindings'])|{'round19/judge/'+n for n in f['self_reference_exclusions']}
actual={p.relative_to(B).as_posix():sha(p) for p in sorted(R.rglob('*')) if p.is_file() and p.name!='controller_manifest.json'}
assert set(actual)==expected,{'missing':sorted(expected-set(actual)),'extra':sorted(set(actual)-expected)}
assert not f['victory'] and not c['full_fixed_D_N_ledger_paid'] and not c['parity_obstacle_bypass_proved']
result={'round':19,'status':'FINAL19_AUXILIARY_IDENTITIES_NO_PARITY_WIN','recorded_utc':datetime.now(timezone.utc).isoformat(),
 'research_goal_active':True,'objective_complete':False,'score':0,'victory':False,
 'new_counts':a['new_counts'],'cumulative_counts':a['cumulative_counts'],
 'previous_artifacts_preserved':1361,'frozen_inputs_verified':307,'historical_dependencies_verified':26,
 'Judge_owned_bindings_verified':145,'independent_audit_invocations':1,'independent_audit_exit_codes':[0],
 'independent_Lean_invocations':11,'independent_Lean_failures':0,'independent_style_warnings':obs['actual_independent_style_warnings'],
 'producer_Lean_invocations':29,'producer_Lean_failures':18,'separate_preLean_launcher_parse_failure':1,
 'new_numeric_canonical_invocations':2,'numeric_canonical_exit_codes':[0,0],'numeric_replays':0,
 'stored_certificates_hash_and_labels_only':obs['stored_certificates_hash_and_labels_only'],
 'root_audit_compiler_numeric_or_logarithmic_sign_invocations':0,'source_A7_and_fixed_acquis_unchanged':True,
 'source_onset':'log N >=10^24','written_rank3_local_onset':'log N >=10^40','source_intermediate_segment_unpaid':True,
 'Gamma_rank_medium_long_capacity_parents_and_full_D_N_unpaid':True,'parity_bypass_certified':False,
 'retained_ledger':'D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0)',
 'semantic_obligations':a['semantic_obligations'],'judge_report_sha256':f['report_sha256'],
 'judge_final_receipt_sha256':sha(J/'final_receipt.json'),'judge_manifest_sha256':sha(J/'manifest.json'),
 'judge_closure_sha256':sha(J/'closure.json'),'audit_receipt_sha256':sha(J/'audit_receipt.json'),
 'original_sources_sha256':inputs['original_documents_sha256'],'bindings_sha256':actual,
 'files_bound':len(actual),'files_with_self':len(actual)+1,'next_protected_artifacts_expected':1361+len(actual)+1,
 'root_full_FINAL_report_read':'16ce4c','manifest_display_truncation_resolved_by_full_metadata_binding_verification':True}
dest=R/'controller_manifest.json'
with dest.open('x',encoding='utf-8') as out: out.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','files_bound','files_with_self','next_protected_artifacts_expected','new_counts','cumulative_counts','victory')}|{'controller_sha256':sha(dest)},ensure_ascii=False,indent=2))
