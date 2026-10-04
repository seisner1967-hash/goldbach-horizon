"""Close actual FINAL18 using stored receipts and hashes only; no audit replay."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from pathlib import Path
from hashlib import sha256
from collections import Counter
from fractions import Fraction
from datetime import datetime, timezone
import json, os, re
B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R = B/'round18'; J = R/'judge'
def read(p): return json.loads(p.read_bytes())
def h(p):
    q = sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): q.update(block)
    return q.hexdigest()
def verify(root, bindings):
    for name, value in bindings.items(): assert h(root/name) == value, name
assert len(sys.argv) == 4, 'Explicit actual FINAL5 report/receipt/manifest SHAs required'
reportsha, receiptsha, manifestsha = sys.argv[1:]
assert h(R/'agent5.md') == reportsha
assert h(J/'final_receipt.json') == receiptsha
assert h(J/'manifest.json') == manifestsha
f = read(J/'final_receipt.json'); m = read(J/'manifest.json'); c = read(J/'closure_receipt.json')
a = read(J/'audit_receipt.json'); inputs = read(J/'input_manifest.json'); launch = read(J/'launch_receipt.json')
assert f['status'] == 'FINAL5_AFTER_COMPLETED_ACTUAL_AUDIT' and m['status'] == 'FINAL_JUDGE18_AUXILIARY_NO_WIN'
assert c['status'] == 'FINAL5_CLOSED_AFTER_ACTUAL_METADATA_EXIT' and c['metadata_exit_code'] == 0
assert f['report_sha256'] == reportsha and f['manifest_sha256'] == manifestsha
assert f['audit_receipt_sha256'] == launch['audit_receipt_sha256'] == h(J/'audit_receipt.json') == '1f694b4e7369ddf12a73970ae8c4ef5cdbc7855669f2179285647b25ce354938'
assert launch['exit_code'] == f['audit_exit_code'] == 0
assert launch['started_at_utc'] == '2026-10-02T22:59:14.940258+00:00'
assert launch['finished_at_utc'] == '2026-10-02T23:02:52.405023+00:00'
assert h(J/'audit.log') == launch['log_sha256'] == '09920b4e459e90bc90f0122c82ce0e04ee3ee31ce91537c414ad0e5dc202c914'
assert len(m['owned_artifacts_sha256']) == m['owned_files']
verify(B,m['owned_artifacts_sha256']); verify(B,c['bindings_sha256'])
assert len(c['bindings_sha256']) == 10
assert len(inputs['round18_sha256']) == 267 and m['frozen_round18_inputs_sha256'] == inputs['round18_sha256']
verify(R,inputs['round18_sha256']); verify(B,inputs['historical_dependencies_sha256'])
assert len(inputs['historical_dependencies_sha256']) == 22 and m['historical_dependencies_sha256'] == inputs['historical_dependencies_sha256']
assert h(J/'input_manifest.json') == a['input_manifest_sha256'] == launch['input_manifest_sha256'] == 'a1e5fa8eaa4d3e455c46f0e1bea20ce516bc0f0473195b6ef0a3e73e7ad2114e'
for path, value in inputs['original_documents_sha256'].items(): assert h(Path(path)) == value
assert h(Path(inputs['lean_executable'])) == inputs['lean_sha256']
assert h(Path(inputs['mathlib_HEAD_path'])) == inputs['mathlib_HEAD_sha256']
for name, value in inputs['judge_code_sha256'].items(): assert h(J/name) == h(J/'preexec'/(name+'.txt')) == value
assert h(J/'authorization.json') == h(J/'preexec/authorization.json.txt') == inputs['authorization_sha256']
new = dict(modules=8,theorems=170,defs=68,structures=4,instances=0,axioms_printed=242)
assert a['new_counts'] == f['new_counts'] == m['new_counts'] == new
assert a['previous_counts'] == dict(modules=22,theorems=337)
assert a['cumulative_counts'] == f['cumulative_counts'] == m['cumulative_counts'] == dict(modules=30,theorems=507)
rows = a['independent_Lean']['modules']; assert len(rows) == 8
assert [r['module'] for r in rows] == [Path(n).stem for n in inputs['new_module_sources']]
assert read(J/'06_independent_Lean_PASS.json') == a['independent_Lean']
total = Counter(); warnings = []
for row in rows:
    n = row['module']; source = Path(row['command'][-1])
    assert row['status'] == 'PASS_FRESH_NEW_LEAN' and row['exit_code'] == 0
    assert read(J/(n+'_receipt.json')) == row
    inv = read(J/(n+'_actual_invocation.json')); start = read(J/(n+'_started.json'))
    assert inv['exit_code'] == 0 and inv['source_sha256'] == start['source_sha256'] == row['source_sha256']
    assert h(Path(row['source_original'])) == h(source) == h(Path(row['source_snapshot'])) == row['source_sha256']
    assert h(J/'preexec'/(n+'.lean.txt')) == row['source_sha256']
    assert h(Path(row['olean'])) == row['olean_sha256'] and h(Path(row['log'])) == row['log_sha256'] == inv['log_sha256']
    assert row['input_manifest_sha256'] == a['input_manifest_sha256']
    assert str(R/'role3') not in row['LEAN_PATH'] and str(R/'role4') not in row['LEAN_PATH']
    log = Path(row['log']).read_text(encoding='utf-8')
    assert not re.search(r'error:|sorryAx', log)
    axes = {name:[s.strip() for s in text.split(',') if s.strip()] for name,text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)}
    axes.update({name:[] for name in re.findall(r"'([^']+)' does not depend on any axioms",log)})
    assert axes == row['axioms'] and len(axes) == len(row['declarations']) == row['axioms_printed']
    assert Counter(n.rsplit('.',1)[-1] for n in axes) == Counter(row['declarations'])
    assert all(set(v) <= {'propext','Classical.choice','Quot.sound'} for v in axes.values())
    ws = [s for s in log.splitlines() if 'warning:' in s]
    assert ws == row['actual_style_warnings']
    assert all(n == 'SeparatedTypeIICount' and "warning: 'push_cast' tactic does nothing" in s for s in ws)
    warnings += ws; total.update(row['declaration_counts'])
assert total == {'theorem':170,'def':68,'structure':4} and len(warnings) == 1
assert sum(r['axioms_printed'] for r in rows) == 242
log = (J/'audit.log').read_text(encoding='utf-8')
assert log.count('FRESH_LEAN_STARTED') == log.count('FRESH_LEAN_PASS') == 8
assert log.count('STAGE_STARTED') == log.count('STAGE_PASS') == 9
assert 'AUDIT_COMPLETE_AUXILIARY_ONLY' in log and not list(J.glob('*continuation*'))
assert a['author_invocations'] == dict(failures=15,invocations=23,warnings=8)
assert a['numeric']['positions'] == 320 and a['numeric']['combined'] == dict(POSITIVE=191,NEGATIVE=83,ZERO=46)
certs = a['numeric']['stored_certificates']; count = Counter()
for bank, cert_rows in certs.items():
    data = read(R/(bank+'.json'))
    for row in cert_rows:
        value = data
        for part in row['json_pointer'].split('/')[1:]:
            key = part.replace('~1','/').replace('~0','~')
            value = value[int(key)] if isinstance(value,list) else value[key]
        enc = json.dumps(value,sort_keys=True,separators=(',',':')).encode()
        assert sha256(enc).hexdigest() == row['stored_certificate_sha256']
        lo, hi = Fraction(value['lower']), Fraction(value['upper']); sign = value['sign']
        assert lo <= hi and sign == row['sign']
        assert (lo > 0 if sign == 'POSITIVE' else hi < 0 if sign == 'NEGATIVE' else sign == 'ZERO' and lo == hi == 0)
        count[sign] += 1
assert count == a['numeric']['combined']
crt = a['distinct_CRT_annex']
assert crt['canonical_invocations'] == 1 and crt['CRT_replays'] == 0 and crt['all_divisor_CRT_checks'] == 1944
assert crt['R4_guards'] == dict(R4a=False,R4b=True,R4c=False) and not crt['R5_applied']
assert crt['J'] == 23185 and crt['JR'] == 234 and crt['corrected_JR'] == 0
assert a['preservation_before'] == a['preservation_after'] == read(J/'07_preservation_after_PASS.json')
assert a['preservation_after']['files'] == 997
registry = read(R/'previous_artifacts_sha256.json')
assert registry['file_count'] == len(registry['sha256']) == 997
verify(B,registry['sha256'])
inventory = {}
for root, dirs, files in os.walk(B):
    dirs[:] = [d for d in dirs if d not in {'.git','.lake','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'} and not (re.fullmatch(r'round\d+',d) and int(d[5:]) >= 18)]
    for name in files:
        p = Path(root)/name
        if p != B/'REPORT.md': inventory[p.relative_to(B).as_posix()] = h(p)
assert inventory == registry['sha256']
for key in ['victory','parity_obstacle_bypass_proved','global_D_N_target_proved','old_numeric_or_Lean_or_PDF_executed','new_numeric_producer_called','W_D_log_or_sign_recalculated']: assert not a[key], key
assert a['source_R6_onset_not_formalized'] and a['D5_D10_D11_not_formalized'] and a['source_intermediate_segment_unpaid'] and a['S_remainder634_T_A_capacity_Gamma_open']
assert f['independent_new_Lean_invocations'] == m['independent_new_Lean_invocations'] == 8
assert f['independent_new_Lean_failures'] == m['independent_new_Lean_failures'] == 0
assert c['audit_or_Lean_stages_replayed'] == c['numeric_producers_called'] == 0
expected = {'round18/'+name for name in inputs['round18_sha256']} | set(m['owned_artifacts_sha256']) | set(c['bindings_sha256']) | {'round18/judge/closure_receipt.json'}
actual = {p.relative_to(B).as_posix():h(p) for p in sorted(R.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.name != 'controller_manifest.json'}
assert set(actual) == expected, dict(missing=sorted(expected-set(actual)),extra=sorted(set(actual)-expected))
dest = R/'controller_manifest.json'; assert not dest.exists()
result = dict(round=18,status='FINAL18_AUXILIARY_CONDITIONAL_NO_PARITY_WIN',recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    research_goal_active=True,objective_complete=False,score=0,victory=False,new_counts=new,cumulative_counts=a['cumulative_counts'],
    previous_artifacts_preserved=997,frozen_inputs_verified=267,historical_dependencies_verified=22,
    Judge_owned_bindings_verified=m['owned_files'],Judge_closure_bindings_verified=10,strict_sign_positions=320,strict_sign_distribution=dict(count),
    independent_audit_invocations=1,independent_audit_exit_codes=[0],independent_Lean_invocations=8,independent_Lean_failures=0,
    independent_style_warnings=warnings,producer_Lean_invocations=23,producer_Lean_failures=15,
    original_numeric_canonical_invocations=3,original_numeric_failures=1,original_unique_isolated_replays=2,
    distinct_CRT_canonical_invocations=1,distinct_CRT_replays=0,distinct_CRT_checks=1944,
    root_metadata_start_observer_failures=1,root_metadata_failure_is_mathematical=False,
    no_test_compiler_numeric_or_audit_reexecution_by_controller=True,
    source_A7_acquired_unchanged=True,source_R6_not_formalized=True,D5_D10_D11_not_formalized=True,
    whole_Gamma_T_A_S_remainder_capacity_and_D_N_unpaid=True,global_D_N_estimated=False,parity_bypass_certified=False,global_impossibility_inferred=False,
    source_onset='log N >= 10^24',written_SS_budget_onset='log N >= 10^36',source_intermediate_segment_unpaid=True,
    retained_ledger='D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',finite_N=100000000,finite_N_is_source_onset_test=False,
    judge_report_sha256=reportsha,judge_final_receipt_sha256=receiptsha,judge_manifest_sha256=manifestsha,
    audit_receipt_sha256=h(J/'audit_receipt.json'),input_manifest_sha256=h(J/'input_manifest.json'),
    original_sources_sha256=inputs['original_documents_sha256'],bindings_sha256=actual,
    files_bound=len(actual),files_with_self=len(actual)+1,next_protected_artifacts_expected=997+len(actual)+1)
with dest.open('x',encoding='utf-8') as out: json.dump(result,out,indent=2,ensure_ascii=False); out.write('\n')
print(json.dumps({k:result[k] for k in ['status','files_bound','files_with_self','previous_artifacts_preserved','next_protected_artifacts_expected','new_counts','cumulative_counts','victory']} | dict(controller_sha256=h(dest)),ensure_ascii=False))
