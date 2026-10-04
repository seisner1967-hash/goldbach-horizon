"""Read-only audit of frozen round12 receipts. No producer imports or execution."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import ast
import json
import os
import re
from datetime import datetime, timezone
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
MANIFEST = HERE / 'input_sha256.json'
inputs = json.loads(MANIFEST.read_bytes())
assert inputs['round'] == 12 and inputs['status'] == 'FINAL_INPUTS_FROZEN'
assert inputs['old_artifacts'] == 487
assert all(v['terminated'] for v in inputs['final_role_signals'].values())
EXPECTED_CONTROLLER = '3860be999898b537fda692534cbf1943225a7aa65e3bb182b48476a5933dd000'
EXPECTED_REGISTRY = '9a0a1010cdc4ad16eeb28b15f960f1d7dd3621bc91cc4d241a8781ccc2e543b1'
SKIP = {'.lake', '.git', '.arbor', '__pycache__', '.pytest_cache', '.mypy_cache', '.ruff_cache'}

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def load(name):
    return json.loads((ROUND / name).read_bytes())

def verify_inputs():
    assert len(inputs['sha256']) == inputs['file_count']
    for name, expected in inputs['sha256'].items():
        assert digest(ROUND / name) == expected, name
    for name, expected in inputs['external_sha256'].items():
        assert digest(Path(name)) == expected, name

def preservation():
    registry_path = ROUND / 'previous_artifacts_sha256.json'
    assert digest(registry_path) == EXPECTED_REGISTRY
    registry = load('previous_artifacts_sha256.json')
    assert registry['file_count'] == len(registry['sha256']) == 487
    assert registry['round11_file_count'] == 82 and registry['last_frozen_round'] == 11
    current = {}
    for directory, children, files in os.walk(BASE, followlinks=False):
        def excluded(name):
            match = re.fullmatch(r'round([0-9]+)', name)
            return name in SKIP or bool(match and int(match.group(1)) >= 12)
        children[:] = sorted(n for n in children if not excluded(n))
        for name in sorted(files):
            path = Path(directory) / name
            if path != BASE / 'REPORT.md':
                current[path.relative_to(BASE).as_posix()] = digest(path)
    assert current == registry['sha256'], 'Protected artifacts changed, disappeared or were added'
    assert current['round11/controller_manifest.json'] == EXPECTED_CONTROLLER
    assert sum(n.startswith('round11/') for n in current) == 82
    originals = {name: dict(expected_sha256=value, actual_sha256=digest(Path(name)))
                 for name, value in inputs['external_sha256'].items()}
    assert all(v['expected_sha256'] == v['actual_sha256'] for v in originals.values())
    return dict(status='PRESERVED', files=487, round11_files=82,
                controller11_sha256=EXPECTED_CONTROLLER, registry_sha256=EXPECTED_REGISTRY,
                originals=originals)

verify_inputs()
before = preservation()
numeric_manifest = load('numeric_manifest.json')
assert digest(ROUND / 'numeric_manifest.json') == inputs['numeric_manifest_sha256']
assert numeric_manifest['file_count'] == len(numeric_manifest['sha256']) == 13
for name, expected in numeric_manifest['sha256'].items():
    assert digest(ROUND / name) == expected, name
for name in ('conservation.py', 'shared.py', 'witness_search.py', 'deletion_checks.py',
             'star_detector_checks.py', 'replay_checks.py'):
    ast.parse((ROUND / name).read_text(encoding='utf-8'), filename=name)

replay = load('numerical_replay.json')
assert replay['status'] == 'PASS_NEW_ROUND12_BYTES_AND_FIELDS_REPLAY'
assert replay['N'] == 100000000 and len(replay['banks']) == 3
EXPECTED_BANKS = {
    'witnesses.json': ('witness_search.py', 'VERIFIED_NEW_ARITHMETIC_WITNESSES_ONLY'),
    'deletion.json': ('deletion_checks.py', 'PASS_NEW_NORMALIZED_DELETION_IDENTITY_ONLY'),
    'star_detector.json': ('star_detector_checks.py', 'PASS_NEW_STAR_AND_GUARDED_DETECTOR_IDENTITIES_ONLY'),
}
assert set(row['receipt'] for row in replay['banks']) == set(EXPECTED_BANKS)
bank_checks, gates = {}, {}
registry = load('previous_artifacts_sha256.json')['sha256']
for row in replay['banks']:
    name = row['receipt']
    script, status = EXPECTED_BANKS[name]
    assert row['script'] == script and row['status'] == status and row['exit_code'] == 0
    assert all(row[key] is True for key in ('all_JSON_fields_equal', 'exact_bytes_equal', 'canonical_unchanged'))
    canonical = (ROUND / name).read_bytes()
    copied = (ROUND / 'isolated_output_probe' / name).read_bytes()
    assert canonical == copied and json.loads(canonical) == json.loads(copied), name
    assert digest(ROUND / script) == row['script_sha256']
    assert sha256(canonical).hexdigest() == row['canonical_sha256'] == row['replay_sha256']
    assert len(canonical) == row['bytes']
    gate = json.loads(canonical)
    assert gate['status'] == status and gate['N'] == 100000000
    assert (gate['alpha'], gate['a'], gate['Q']) == (100, 3163, 999999)
    assert gate['script_sha256'] == digest(ROUND / script)
    assert gate['shared_sha256'] == digest(ROUND / 'shared.py')
    for relative, expected in gate['imports'].items():
        assert digest(BASE / relative) == expected, relative
        if not relative.startswith('round12/'):
            assert registry[relative] == expected
    for key in ('global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory'):
        assert gate[key] is False
    for key in ('conservation_before', 'conservation_after'):
        assert gate[key]['status'] == 'PRESERVED' and gate[key]['files'] == 487
    gates[name] = gate
    bank_checks[name] = dict(status=status, script_sha256=row['script_sha256'],
                            receipt_sha256=row['canonical_sha256'], bytes=len(canonical),
                            all_fields_equal=True, all_bytes_equal=True,
                            producer_executed_by_judge=False)
for name, expected in replay['artifact_sha256'].items():
    assert digest(ROUND / name) == expected
for key in ('conservation_before', 'conservation_after'):
    assert replay[key]['status'] == 'PRESERVED' and replay[key]['files'] == 487
for key in ('old_passed_banks_executed', 'old_production_modified', 'bytecode_written',
            'global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory'):
    assert replay[key] is False

falsifiers, signs = {}, {}
def walk(node, path):
    if isinstance(node, dict):
        if node.get('status') == 'ERROR_FALSIFIER':
            falsifiers[path] = node['status']
        if 'sign' in node and 'lower' in node and 'upper' in node:
            sign = node['sign']
            lo, hi = Fraction(node['lower']), Fraction(node['upper'])
            assert lo <= hi and sign in ('POSITIVE', 'NEGATIVE', 'ZERO'), path
            assert (lo > 0 if sign == 'POSITIVE' else hi < 0 if sign == 'NEGATIVE' else lo == hi == 0), path
            signs[path] = sign
        assert node.get('global_no_go', False) is False
        for key, value in node.items():
            walk(value, path + '.' + str(key))
    elif isinstance(node, list):
        for i, value in enumerate(node):
            walk(value, path + '.' + str(i))
for name, gate in gates.items():
    walk(gate, name)
EXPECTED_FALSIFIERS = {
    'deletion.json.matching_model.false_unit_guard_omitted',
    'deletion.json.selected_polynomial_probe',
    'deletion.json.false_guardless_deletion',
    'deletion.json.false_denominator_omitted',
    'deletion.json.false_unweighted_prime_deletion',
    'deletion.json.false_short_cofactor_completion',
    'star_detector.json.complete_star.false_full_star_favorable',
    'star_detector.json.false_free_inverse_log_gain.J1_two_small',
    'star_detector.json.false_free_inverse_log_gain.J1_three_small',
    'star_detector.json.false_properpower_correction_omitted',
}
assert set(falsifiers) == EXPECTED_FALSIFIERS
deletion, star = gates['deletion.json'], gates['star_detector.json']
assert deletion['matching_model']['status'] == 'PASS_NEW_FINITE_MATCHING_ROOT_IDENTITY_ONLY'
assert deletion['same_selected_m_in_both_finite_transfer_sides'] is True
assert deletion['properpower_first_axis_retained'] is True and deletion['mu_n_squared_added'] is False
assert deletion['S_N_not_evaluated'] is True and deletion['denominator_log_m_crossmultiplied_exactly'] is True
assert deletion['endpoint']['m'] == 1 and deletion['endpoint']['mu_m'] == 1
assert deletion['selected_polynomial_probe']['selected_m'] == [29, 561]
assert deletion['selected_polynomial_probe']['global_polynomial_property_tested'] is False
assert deletion['matching_model']['false_unit_guard_omitted']['actual_rho'] == 5
assert len(deletion['points']) == 6
for point in deletion['points'].values():
    identity = point['normalized_identity_after_log_m']
    assert identity['lhs'] == identity['rhs']
    transfer = point['guarded_G_transfer_after_log_m']
    assert transfer['constant'] == transfer['transferred_constant'] and transfer['S'] == transfer['transferred_S']
assert deletion['points']['new_properpower_axis']['n'] == 8017**2
assert deletion['points']['new_properpower_axis']['Lambda_N'] == {'8017': '1'}
assert deletion['points']['new_properpower_axis']['theta_N'] == {}
assert deletion['points']['new_properpower_axis']['complementary_cofactor_sectors']['short_S'] == {}
assert all(p['c'] > 3163 for p in deletion['points']['new_properpower_axis']['pairs'])
assert star['properpowers_first_axis_retained'] is True and star['mu_n_squared_added'] is False
assert star['detector_pointwise_positive_not_assumed'] is True
complete = star['complete_star']
assert complete['status'] == 'PASS_NEW_FULL_THREE_INCIDENCE_CAPACITY_ONLY'
assert complete['complete_X'] == [1, 3, 7] and complete['C_t'] == 9
assert complete['whole_actual_sign']['sign'] == 'POSITIVE'
assert complete['Kstar_constant_sign']['sign'] == complete['Kstar_S_sign']['sign'] == 'POSITIVE'
assert complete['bulk_cut_closed_under_prime_deletion'] is True
assert complete['nonbulk_complement_not_estimated'] is True
assert complete['matching_actual_W_terms_retained'] is True
assert complete['analytical_source_onset_assumed_at_N'] is False
assert all(p['all_k_equals_ge2'] for p in complete['points'].values())
assert all(c['in_cut'] for c in complete['prime_deletion_children'] if c['bulk'])
assert any(c['complementary_nonbulk_term_not_paid'] for c in complete['prime_deletion_children'])
for coverage in star['false_free_inverse_log_gain'].values():
    assert coverage['complete_L1_V'] == '1'
    assert coverage['absolute_numerator'] == coverage['log_m']
proper = star['detector_points']['new_second_axis_properpower']
assert proper['m'] == 17**3 and proper['n'] == 99995087
assert proper['Lambda_N'] == proper['theta_N'] == {'99995087': '1'}
assert proper['E_times_log_m'] == {}
assert proper['V_times_log_m'] == proper['P_times_log_m'] == {'17': '1'}
assert proper['V_and_P_value'] == '1/3'
verify_inputs()
after = preservation()
assert before == after
receipt = dict(round=12, status='REJECTED_BEFORE_LEAN_WITH_VALID_GUARDED_IDENTITIES',
    recorded_at_utc=datetime.now(timezone.utc).isoformat(), input_manifest=str(MANIFEST),
    input_manifest_sha256=digest(MANIFEST), input_sha256=inputs['sha256'],
    external_sha256=inputs['external_sha256'], final_role_signals=inputs['final_role_signals'],
    numerical_audit_mode='READ_ONLY_EXISTING_ISOLATED_REPLAY_FIELDS_AND_BYTES',
    numerical_producers_invoked_by_judge=False, numerical_replay_receipt_sha256=digest(ROUND / 'numerical_replay.json'),
    bank_audits=bank_checks, distinct_contract_statuses={k: v['status'] for k, v in gates.items()},
    falsifiers=falsifiers, falsifier_count=len(falsifiers), rational_signs=signs,
    rational_sign_count=len(signs), strict_signs=True, unresolved_signs=0,
    preservation_before=before, preservation_after=after,
    lean_invoked=False, compiler_failure_fabricated=False, new_lean_modules=0, new_lean_conclusions=0,
    cumulative_auxiliary_modules=13, cumulative_auxiliary_conclusions=169,
    old_banks_rerun=False, old_lean_rerun=False, old_pdf_rerendered=False,
    finite_N=100000000, source_adaptive_u_min='10^24', finite_witness_is_source_onset_test=False,
    global_no_go=False, victory=False, score=0,
    semantic_open_obligations=['Compensation between genuinely signed physical stars and nonbulk complements',
        'Mobius(c) times actual Lambda_N(N-pc) and matching S(cN) model unestimated',
        'Prime diagonal c=1, original reference -S(N)N, and long cofactors c>a retained',
        'H2, singleton and face terms, J0/J1, BV extra onset and 2 max(e,0) unpaid'],
    judge_scripts_sha256={n: digest(HERE / n) for n in ('audit-judge.ps1', 'run-audit.py', 'freeze-inputs.py')})
(HERE / 'judge_receipt.json').write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=receipt['status'], preserved=487, bank_bytes_audited=3,
    falsifiers=len(falsifiers), rational_signs=len(signs), lean_invoked=False,
    new_conclusions=0, cumulative_conclusions=169, victory=False, score=0), indent=2))
