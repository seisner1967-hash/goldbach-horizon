"""Bind explicit FINAL16 evidence; no mathematical producer, compiler or audit rerun."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
from collections import Counter
import json, os, re

BASE = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
RND = BASE / 'round16'
JUDGE = RND / 'judge'
def sha(p):
    h = sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda: f.read(1048576), b''): h.update(chunk)
    return h.hexdigest()
def read(p): return json.loads(p.read_bytes())
def verify_map(root, mapping):
    for n, h in mapping.items(): assert sha(root / n) == h, n

assert len(sys.argv) == 3, 'Explicit FINAL5 report and Judge receipt hashes required'
report_sha, receipt_sha = sys.argv[1:]
assert sha(RND / 'agent5.md') == report_sha
assert sha(JUDGE / 'judge_receipt.json') == receipt_sha
j = read(JUDGE / 'judge_receipt.json')
assert j['status'] == 'PARTIAL_CANONICAL_REAL_SINGULAR_MARGIN_COMPILED_GLOBAL_INCIDENCE_OPEN'
assert j['score'] == 0 and j['victory'] is False
assert j['lean_invoked'] and j['source_A7_certified'] and j['canonical_p0_certified']
assert j['real_tprod_convergence_and_tail_proved']
assert j['source_A9_Lean_certified'] is False and j['global_D_N_estimated'] is False
assert j['parity_bypass_certified'] is False
assert (j['new_lean_modules'], j['new_lean_conclusions'], j['new_lean_definitions']) == (2, 36, 8)
assert (j['cumulative_auxiliary_modules'], j['cumulative_auxiliary_conclusions']) == (17, 244)
for key in ('numerical_producers_invoked_by_judge', 'old_banks_replayed',
            'old_Lean_or_dependency_rebuilt', 'old_PDF_rerendered', 'finite_test_is_source_onset_test'):
    assert j[key] is False, key
assert j['preservation_before'] == j['preservation_after'] and j['preservation_after']['files'] == 701
assert j['unresolved_signs'] == j['floating_values'] == 0 and j['strict_rational_interval_signs']
assert j['rational_sign_count'] == len(j['rational_signs']) == 1879
assert Counter(j['rational_signs'].values()) == j['rational_sign_distribution'] == dict(POSITIVE=654, NEGATIVE=95, ZERO=1130)
assert j['falsifier_count'] == len(j['falsifiers']) == 4
assert len(j['promotions_without_counterexample']) == 1 and j['actual_numeric_failures'] == 0
assert len(j['producer_Lean_failures']) == 9 and all(x['exit_code'] == 1 and not x['parity_diagnostic'] for x in j['producer_Lean_failures'])
assert j['producer_role3_compilations'] == 13 and j['producer_role3_API_probes'] == 1
assert j['producer_role3_candidate_compilations'] == 12 and j['producer_role3_PASS_attempts'] == [4,9,11,13]
assert j['producer_role4_compilations'] == 1

inputs = read(JUDGE / 'input_sha256.json')
assert sha(JUDGE / 'input_sha256.json') == j['input_manifest_sha256']
assert inputs['sha256'] == j['input_sha256'] and inputs['file_count'] == len(inputs['sha256']) == 78
assert len(inputs['reports']) == 5 and all(v['terminated'] for v in inputs['final_role_signals'].values())
verify_map(RND, inputs['sha256'])
for n,h in inputs['external_sha256'].items(): assert sha(Path(n)) == h, n
verify_map(JUDGE, j['judge_scripts_sha256'])
jf = read(JUDGE / 'final_receipt.json')
assert jf['report_sha256'] == report_sha and jf['own_bound_files'] == len(jf['sha256']) == 18
assert jf['final_audit_invocations'] == 1 and jf['final_audit_exit_code'] == 0
verify_map(RND, jf['sha256'])

registry = read(RND / 'previous_artifacts_sha256.json')
assert registry['file_count'] == len(registry['sha256']) == 701
assert sha(RND / 'previous_artifacts_sha256.json') == j['preservation_after']['registry_sha256']
verify_map(BASE, registry['sha256'])
actual = {}
for top, dirs, files in os.walk(BASE):
    dirs[:] = [d for d in dirs if d not in ('.git','.lake','.arbor','__pycache__')
               and not (re.fullmatch(r'round\d+', d) and int(d[5:]) >= 16)]
    for n in files:
        p = Path(top) / n
        if p == BASE / 'REPORT.md': continue
        actual[p.relative_to(BASE).as_posix()] = sha(p)
assert actual == registry['sha256'], 'Exact old inventory mismatch'

numeric = read(RND / 'numeric_manifest.json')
assert sha(RND / 'numeric_manifest.json') == j['numeric_manifest_sha256']
assert numeric['status'] == 'FINAL_FROZEN_NEW_ROUND16_NUMERIC_PARTIAL'
assert numeric['files'] == len(numeric['sha256']) == j['numeric_bindings'] == 30
assert numeric['new_banks'] == numeric['new_canonical_attempts'] == numeric['isolated_replays'] == 2
assert numeric['real_failed_attempts'] == 0 and numeric['numeric_role_Lean_called'] is False
verify_map(RND, numeric['sha256']); verify_map(RND, numeric['reports_FINAL_sha256'])
for name, a in j['bank_audits'].items():
    assert a['all_bytes_identical'] and a['all_fields_identical'] and a['existing_isolated_replay_verified']
    assert a['producer_executed_by_judge'] is False
    assert sha(RND / (name + '.json')) == sha(RND / ('isolated_' + name) / (name + '.json')) == a['gate_sha256']
    assert sha(RND / (name + '_checks.py')) == a['producer_sha256']
for role, thm, defs in ((3,27,8),(4,9,0)):
    f = read(RND / f'role{role}/final_receipt.json')
    assert f['theorem_count'] == thm and f['definition_count'] == defs and not f['victory']
    for asset in f['files']:
        p = Path(asset['path']); assert sha(p) == asset['sha256'] and p.stat().st_size == asset['bytes']
    assert sha(Path(f['report_path'])) == f['report_sha256']

assert j['independent_compile_invocations'] == len(j['independent_new_compiles']) == 2
assert j['independent_compile_failures'] == 0
for row in j['independent_new_compiles']:
    assert row['exit_code'] == row['errors'] == row['warnings'] == 0 and row['axioms_standard_only']
    assert row['fresh_source_copy'] and row['old_dependencies_rebuilt'] is False
    m = row['module']
    assert sha(JUDGE / 'build' / (m + '.lean')) == row['source_sha256']
    assert sha(JUDGE / 'build' / (m + '.olean')) == row['olean_sha256']
    assert sha(JUDGE / (m + '_fresh.log')) == row['log_sha256']
    fresh = read(JUDGE / (m + '_fresh_receipt.json'))
    assert all(row[k] == v for k,v in fresh.items())
launch = read(JUDGE / 'audit_launch_receipt.json')
assert launch['status'] == 'OBSERVED_SINGLE_FINAL_AUDIT' and launch['exit_code'] == 0 and launch['invocations'] == 1
assert launch['audit_reexecuted_for_logging'] is False
assert launch['numeric_producer_executed_by_judge'] is False and launch['old_Lean_or_dependency_recompiled'] is False
assert sha(JUDGE / 'audit_launch.log') == launch['log_sha256']
assert sha(JUDGE / 'run-audit.py') == launch['script_sha256']
assert launch['input_manifest_sha256'] == j['input_manifest_sha256']

bindings = {p.relative_to(RND).as_posix(): sha(p) for p in sorted(RND.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts and p.name != 'controller_manifest.json'}
manifest = dict(round=16, status=j['status'], recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    research_goal_active=True, objective_complete=False, victory=False, score=0,
    lean_invoked=True, new_lean_modules=2, new_lean_conclusions=36, new_lean_definitions=8,
    cumulative_auxiliary_modules=17, cumulative_auxiliary_conclusions=244,
    previous_artifacts_preserved=701, frozen_input_bindings_verified=78, numeric_bindings_verified=30,
    isolated_output_hashes_verified=2, new_candidate_banks=2, independent_new_Lean_compiles=2,
    no_test_reexecution_by_controller=True, independent_judge_mode='stored full numerical copies and two fresh new-module compiles only',
    local_falsifiers=4, strict_rational_sign_positions=1879, rational_sign_distribution=j['rational_sign_distribution'],
    actual_failed_numeric_attempts=[], actual_failed_lean_attempts=j['producer_Lean_failures'],
    finite_N=100000000, source_adaptive_onset='u>=10^24', finite_witness_is_source_onset_test=False,
    source_A7_certified=True, canonical_p0_certified=True, source_A9_Lean_certified=False,
    real_tprod_convergence_and_tail_proved=True, global_D_N_estimated=False, global_impossibility_inferred=False,
    retained_ledger='D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',
    partial_mechanism='canonical least missing odd prime and actual singular-series margin 1/144; local TypeI correction with literal price',
    weighted_covariance_not_estimated=True, source_prime_incidence_not_estimated=True, global_parent_reuse_not_paid=True,
    typei=j['typei'], capacity=j['capacity'], unpaid=j['semantic_open_obligations'],
    judge_report_sha256=report_sha, judge_receipt_sha256=receipt_sha, bindings_sha256=bindings,
    judge_final_receipt_sha256=sha(JUDGE/'final_receipt.json'), judge_launch_receipt_sha256=sha(JUDGE/'audit_launch_receipt.json'),
    original_sources_sha256=inputs['external_sha256'])
dest = RND / 'controller_manifest.json'; assert not dest.exists(), 'FINAL16 controller already frozen'
dest.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=manifest['status'], files_bound=len(bindings), previous_verified=701,
    next_protected_expected=701+len(bindings)+1, retained_conclusions=244, victory=False, controller_sha256=sha(dest))))
