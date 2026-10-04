"""Root closure: hashes, stored receipts and declarations only; no audit rerun."""
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from collections import Counter
from datetime import datetime,timezone
import json,os,re
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round17';J=R/'judge'
def h(p):
    q=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):q.update(block)
    return q.hexdigest()
def read(p):return json.loads(p.read_bytes())
def verify(root,mp):
    for name,value in mp.items():assert h(root/name)==value,name
assert len(sys.argv)==4,'Explicit FINAL5 report/receipt/manifest SHAs required'
reportsha,receiptsha,manifestsha=sys.argv[1:]
assert h(R/'agent5.md')==reportsha=='02a794b5006ea102fd450023286e867b8eb82c15d12487ef00062d9e8a09f1c6'
assert h(J/'final_receipt.json')==receiptsha=='5768312d9bcfe7ae491ac227d25bd8efde59387f4293ac8990ad709ba6d3eaa0'
assert h(J/'manifest.json')==manifestsha=='492e552a774e2fed9de93a64de9e9a90f3ddb7fbcedc72b500f7784ddc1047d0'
f=read(J/'final_receipt.json');m=read(J/'manifest.json');a=read(J/'audit_receipt.json');inputs=read(J/'input_sha256.json')
assert h(J/'audit_receipt.json')==f['audit_receipt_sha256']=='f44584f6a6a39679ad61108fe2d660d05f64769301a9f7c8f71b0227f008117e'
assert f['status']=='FINAL_ROUND17_INDEPENDENT_JUDGE_PARTIAL' and f['score']==0 and not f['victory']
assert f['new_fresh_Lean_invocations']==f['new_fresh_Lean_exit_zero']==5 and f['new_fresh_Lean_exit_nonzero']==0
assert m['files']==len(m['sha256_relative_judge'])==52
assert f['own_asset_count_before_final_receipt']==len(f['own_assets_sha256'])==51
verify(J,m['sha256_relative_judge']);verify(J,f['own_assets_sha256'])
assert m['receipt_sha256']==receiptsha and m['report_sha256']==f['report_sha256']==reportsha
assert h(J/'input_sha256.json')==a['input_manifest_sha256']==f['input_manifest_sha256']=='40076625c36a04c5cef48ece8ee2d4fe625715cfbe1bf06364ae3da5b182bcb1'
assert inputs['files']==a['frozen_files']==len(inputs['sha256'])==143
assert inputs['sha256']==a['input_sha256'];verify(R,inputs['sha256'])
for group in ['external_originals_sha256','fixed_contexts_sha256']:
    for path,value in inputs[group].items():assert h(Path(path))==value,path
assert h(Path(inputs['lean_executable']))==inputs['lean_sha256']
imap=read(J/'input_map.json');assert h(J/'input_map.json')==f['input_map_sha256']
assert imap['author_inputs143']==a['input_sha256'] and imap['originals_and_fixed_contexts']==inputs
assert a['new_counts']==f['new_counts']==dict(modules=5,theorems=93,defs=40,instances=1,axioms_printed=134)
assert a['previous_counts']==dict(modules=17,theorems=244)
assert a['cumulative_counts']==f['cumulative_counts']==dict(modules=22,theorems=337)
assert f['independent_audit_invocations']==a['independent_audit_attempts']==3
attempts=[('launch_receipt.json','run-audit.py','audit_source.py.txt','audit.log','launch_started.json',1),
          ('continuation_receipt.json','continue-audit.py','continuation_source.py.txt','continuation.log','continuation_started.json',1),
          ('continuation02_receipt.json','continue-audit02.py','continuation02_source.py.txt','continuation02.log','continuation02_started.json',0)]
for receipt,source,snapshot,log,marker,code in attempts:
    x=read(J/receipt);assert x['exit_code']==code and x['post_PASS_rerun_forbidden']
    assert h(J/source)==h(J/snapshot)==x['source_sha256']==x['snapshot_sha256']
    assert h(J/log)==x['log_sha256']
    assert h(J/marker)==x.get('started_marker_sha256',x.get('started_marker_sha256'))
    assert x['input_manifest_sha256']==a['input_manifest_sha256']
assert [x['exit_code'] for x in imap['audit_attempts']]==[1,1,0]
assert m['audit_invocations3_exit_codes']==[1,1,0]
for name in ['audit.log','continuation.log']:
    assert 'FRESH_LEAN_STARTED' not in (J/name).read_text(encoding='utf-8')
lastlog=(J/'continuation02.log').read_text(encoding='utf-8')
assert lastlog.count('FRESH_LEAN_STARTED')==lastlog.count('FRESH_LEAN_PASS')==5 and 'AUDIT_COMPLETE_PARTIAL_ONLY' in lastlog
assert f['real_Judge_technical_pre_Lean_failures']==2
assert not read(J/'preparation_incident.json')['audit_started']
allowed={'propext','Classical.choice','Quot.sound'}
mods=a['independent_new_compiles'];assert len(mods)==5
assert [x['module'] for x in mods]==['FourFormRoots','PowersetMoment','SelbergFourForms','FourFormTruncation','FourFormCollisionLoss']
tot=Counter()
for x in mods:
    assert x['exit_code']==0
    assert h(Path(x['source_original']))==h(Path(x['source']))==h(Path(x['snapshot']))==x['source_sha256']==x['snapshot_sha256']
    assert h(Path(x['output']))==x['olean_sha256'] and h(Path(x['log']))==x['log_sha256']
    log=Path(x['log']).read_text(encoding='utf-8');assert not re.search(r'error:|warning:|sorryAx',log)
    axioms={n:[v.strip() for v in vs.split(',') if v.strip()] for n,vs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)}
    axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",log)})
    assert axioms==x['axioms'] and len(axioms)==x['axioms_printed']
    for axes in axioms.values():assert set(axes)<=allowed
    src=Path(x['source']).read_text(encoding='utf-8');assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',src)
    for key in ['theorems','defs','instances','axioms_printed']:tot[key]+=x[key]
assert tot==dict(theorems=93,defs=40,instances=1,axioms_printed=134)
assert read(J/'independent_compilations.json')['modules']==mods
assert imap['modules_in_real_import_order']==mods
assert a['producer_Lean_invocations']==30 and len(a['producer_Lean_failures'])==a['producer_Lean_real_failures']==23
assert a['producer_numeric_real_failures']==1 and len(a['producer_PASS15_warning'])==1
for x in a['producer_Lean_failures']:
    assert x['exit_code']==1 and not x['analytic_parity_failure']
    assert h(Path(x['snapshot']))==x['snapshot_sha256'] and h(Path(x['log']))==x['log_sha256']
cert=read(J/'rational_certificates.json')
for key,num,distribution in [('initial',390,dict(POSITIVE=242,NEGATIVE=62,ZERO=86)),('distinct_C4',64,dict(POSITIVE=54,NEGATIVE=10))]:
    assert len(cert[key])==num and Counter(x['sign'] for x in cert[key].values())==distribution
    for x in cert[key].values():
        lo,hi=Fraction(x['lower']),Fraction(x['upper']);assert lo<=hi
        assert (lo>0 if x['sign']=='POSITIVE' else hi<0 if x['sign']=='NEGATIVE' else lo==hi==0)
assert a['rational_signs']==390 and a['distinct_C4_rational_signs']==64
assert a['rational_sign_distribution']==f['initial_positions390']==dict(POSITIVE=242,NEGATIVE=62,ZERO=86)
assert a['distinct_C4_sign_distribution']==f['distinct_C4_positions64']==dict(POSITIVE=54,NEGATIVE=10)
assert a['preservation_before']['files']==a['preservation_after']['files']==f['preservation799']['files']==799
assert f['preservation799']==a['preservation_after']
registry=read(R/'previous_artifacts_sha256.json');assert registry['file_count']==len(registry['sha256'])==799
verify(B,registry['sha256'])
inventory={}
for root,dirs,files in os.walk(B):
    dirs[:]=[d for d in dirs if d not in {'.git','.lake','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'} and not (re.fullmatch(r'round\d+',d) and int(d[5:])>=17)]
    for name in files:
        p=Path(root)/name
        if p!=B/'REPORT.md':inventory[p.relative_to(B).as_posix()]=h(p)
assert inventory==registry['sha256']
for key in ['author_FINAL_files_changed','old_or_new_numeric_producer_called','W_or_log_sign_recomputed','old_Lean_or_dependency_compiled','availability_assumed','parity_obstacle_bypass_proved','victory']:
    assert not a[key],key
assert a['actual_G_h_rho_unconditional_definitions'] and a['G_lower_derived_conditional_on_independent_prime_log_input']
assert a['source_C4_full_constants_Mertens_totient_CRT_plus1_C6_unformalized'] and a['whole_D_N_uncontrolled']
assert a['A7_acquired16_unchanged'] and a['A_S_global_capacity_Gamma_full_TypeII_unpaid']
expected=set(inputs['sha256'])|{'judge/'+name for name in m['sha256_relative_judge']}|{'judge/manifest.json','agent5.md'}
actual={p.relative_to(R).as_posix():h(p) for p in sorted(R.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.name!='controller_manifest.json'}
assert set(actual)==expected and len(actual)==197
dest=R/'controller_manifest.json';assert not dest.exists(),'FINAL17 controller already frozen'
manifest=dict(round=17,status='FINAL17_PARTIAL_ACTUAL_G_SELBERG_CERTIFIED_GLOBAL_OPEN',recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    research_goal_active=True,objective_complete=False,score=0,victory=False,new_lean_modules=5,new_lean_conclusions=93,new_lean_definitions=40,new_lean_instances=1,
    cumulative_auxiliary_modules=22,cumulative_auxiliary_conclusions=337,previous_artifacts_preserved=799,frozen_input_bindings_verified=143,
    initial_numeric_bindings_verified=33,distinct_C4_bindings_verified=15,Judge_bindings_verified=52,strict_rational_sign_positions=454,
    initial_rational_positions390=a['rational_sign_distribution'],distinct_C4_rational_positions64=a['distinct_C4_sign_distribution'],
    independent_audit_invocations=3,independent_audit_exit_codes=[1,1,0],Judge_pre_Lean_technical_failures=2,independent_new_Lean_compiles=5,Judge_Lean_failures=0,
    producer_Lean_invocations=30,producer_Lean_real_failures=23,producer_PASS15_warning_preserved=True,actual_failed_lean_attempts=a['producer_Lean_failures'],
    actual_numeric_failures=1,canonical_new_banks=2,distinct_C4_annex=True,no_test_compiler_or_audit_reexecution_by_controller=True,
    actual_G_principal_and_weights_derived=True,actual_Mobius_and_four_form_roots_bound=True,conditional_actual_G_collision_loss_half_proved=True,
    analytic_prime_log_sum_input_remains=True,full_source_C4_not_Lean_certified=True,C6_T_A_T_S_Gamma_whole_TypeII_global_unpaid=True,
    source_A7_acquired_unchanged=True,global_D_N_estimated=False,parity_bypass_certified=False,global_impossibility_inferred=False,
    finite_N=100000000,source_onset='log N >= 10^24',finite_N_is_source_onset_test=False,
    retained_ledger='D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',
    bank_audits=a['bank_audits'],distinct_C4_audit=a['distinct_C4_bank_audit'],judge_report_sha256=reportsha,judge_final_receipt_sha256=receiptsha,
    judge_manifest_sha256=manifestsha,audit_receipt_sha256=h(J/'audit_receipt.json'),input_manifest_sha256=h(J/'input_sha256.json'),
    original_sources_sha256=inputs['external_originals_sha256'],bindings_sha256=actual,next_protected_artifacts_expected=997)
dest.write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=manifest['status'],files_bound=197,with_self=198,previous_verified=799,next_protected_expected=997,
                     new_modules=5,new_theorems=93,cumulative_modules=22,cumulative_theorems=337,controller_sha256=h(dest),victory=False)))
