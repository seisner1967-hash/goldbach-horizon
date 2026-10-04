"""FINAL-input-only round13 Judge: read-only numerical audit, then fresh Lean."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import ast
import importlib.util
import json
import os
import re
from datetime import datetime, timezone
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

JUDGE = Path(__file__).resolve().parent
ROUND = JUDGE.parent
BASE = ROUND.parent
MANIFEST = JUDGE / 'input_sha256.json'
inputs = json.loads(MANIFEST.read_bytes())
assert inputs['round'] == 13 and inputs['status'] == 'FINAL_INPUTS_FROZEN'
assert len(inputs['reports']) == 5 and all(s['terminated'] for s in inputs['final_role_signals'].values())
EXPECTED_REGISTRY = '02c04c95e5348369b9c4577ac3a14e5b4b89e15f53e142e75a37e58b6bde7351'
EXPECTED_CONTROLLER = 'd84cca25948c6794764f3afbc7b6fa23d46faa4152fdad17f2f87da69929a400'
SKIP = {'.lake', '.git', '.arbor', '__pycache__', '.pytest_cache', '.mypy_cache', '.ruff_cache'}

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def load(name):
    return json.loads((ROUND / name).read_bytes())

def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

def verify_inputs():
    assert len(inputs['sha256']) == inputs['file_count']
    for name, expected in inputs['sha256'].items():
        assert sha(ROUND / name) == expected, name
    for name, expected in inputs['external_sha256'].items():
        assert sha(Path(name)) == expected, name

def preservation():
    registry = load('previous_artifacts_sha256.json')
    assert sha(ROUND / 'previous_artifacts_sha256.json') == EXPECTED_REGISTRY
    assert registry['file_count'] == len(registry['sha256']) == 514
    assert registry['round12_file_count'] == 27 and registry['last_frozen_round'] == 12
    current = {}
    for directory, children, files in os.walk(BASE, followlinks=False):
        def excluded(name):
            match = re.fullmatch(r'round([0-9]+)', name)
            return name in SKIP or bool(match and int(match.group(1)) >= 13)
        children[:] = sorted(n for n in children if not excluded(n))
        for name in sorted(files):
            path = Path(directory) / name
            if path != BASE / 'REPORT.md':
                current[path.relative_to(BASE).as_posix()] = sha(path)
    assert current == registry['sha256'], 'Protected artifacts changed, disappeared or were added'
    assert current['round12/controller_manifest.json'] == EXPECTED_CONTROLLER
    assert sum(n.startswith('round12/') for n in current) == 27
    external = {n: dict(expected_sha256=v, actual_sha256=sha(Path(n)))
                for n, v in inputs['external_sha256'].items()}
    assert all(v['expected_sha256'] == v['actual_sha256'] for v in external.values())
    return dict(status='PRESERVED', files=514, round12_files=27, previous_protected_files=487,
        controller12_sha256=EXPECTED_CONTROLLER, registry_sha256=EXPECTED_REGISTRY, external=external)

verify_inputs()
before = preservation()
numeric_manifest = load('numeric_manifest.json')
assert sha(ROUND / 'numeric_manifest.json') == inputs['numeric_manifest_sha256']
assert numeric_manifest['status'] == 'FROZEN_NUMERICAL_INPUTS_TERMINATED'
assert numeric_manifest['file_count'] == len(numeric_manifest['sha256']) == 11
for name, expected in numeric_manifest['sha256'].items():
    assert sha(ROUND / name) == expected, name
for name in ('conservation.py', 'shared.py', 'exchange_checks.py', 'operator_checks.py', 'replay_checks.py'):
    ast.parse((ROUND / name).read_text(encoding='utf-8'), filename=name)
replay = load('numerical_replay.json')
assert replay['status'] == 'PASS_NEW_ROUND13_BYTES_AND_FIELDS_REPLAY'
assert replay['N'] == 100000000 and len(replay['banks']) == 2
expected_banks = {
    'exchange.json': ('exchange_checks.py', 'PASS_NEW_CROSS_KERNEL_EXCHANGE_IDENTITY_ONLY'),
    'operator.json': ('operator_checks.py', 'PASS_NEW_ACTUAL_OPERATOR_IDENTITIES_ONLY'),
}
assert set(r['receipt'] for r in replay['banks']) == set(expected_banks)
gates, bank_audits = {}, {}
registry = load('previous_artifacts_sha256.json')['sha256']
for row in replay['banks']:
    name = row['receipt']
    script, status = expected_banks[name]
    assert row['script'] == script and row['status'] == status and row['exit_code'] == 0
    assert all(row[k] is True for k in ('all_JSON_fields_equal', 'exact_bytes_equal', 'canonical_unchanged'))
    canonical = (ROUND / name).read_bytes()
    copied = (ROUND / 'isolated_output_probe' / name).read_bytes()
    assert canonical == copied and json.loads(canonical) == json.loads(copied)
    assert sha(ROUND / script) == row['script_sha256']
    assert sha256(canonical).hexdigest() == row['canonical_sha256'] == row['replay_sha256']
    assert len(canonical) == row['bytes']
    gate = json.loads(canonical)
    assert gate['status'] == status and gate['N'] == 100000000
    assert (gate['alpha'], gate['a'], gate['Q']) == (100, 3163, 999999)
    assert gate['script_sha256'] == sha(ROUND / script) and gate['shared_sha256'] == sha(ROUND / 'shared.py')
    for relative, expected in gate['imports'].items():
        assert sha(BASE / relative) == expected
        if not relative.startswith('round13/'):
            assert registry[relative] == expected
    for key in ('global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory'):
        assert gate[key] is False
    for key in ('conservation_before', 'conservation_after'):
        assert gate[key]['status'] == 'PRESERVED' and gate[key]['files'] == 514
    gates[name] = gate
    bank_audits[name] = dict(status=status, script_sha256=row['script_sha256'], receipt_sha256=row['canonical_sha256'],
        bytes=len(canonical), all_fields_equal=True, all_bytes_equal=True, producer_executed_by_judge=False)
for name, expected in replay['artifact_sha256'].items():
    assert sha(ROUND / name) == expected
for key in ('old_passed_banks_executed', 'old_production_modified', 'bytecode_written',
            'global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory'):
    assert replay[key] is False

falsifiers, signs = {}, {}
def walk(node, path):
    assert not isinstance(node, float), ('Floating value in exact gate', path)
    if isinstance(node, dict):
        if node.get('status') == 'ERROR_FALSIFIER':
            falsifiers[path] = node['status']
        if 'sign' in node and 'lower' in node and 'upper' in node:
            sign = node['sign']
            lo, hi = Fraction(node['lower']), Fraction(node['upper'])
            assert lo <= hi and sign in ('POSITIVE', 'NEGATIVE', 'ZERO')
            assert (lo > 0 if sign == 'POSITIVE' else hi < 0 if sign == 'NEGATIVE' else lo == hi == 0)
            signs[path] = sign
        assert node.get('global_no_go', False) is False
        for key, value in node.items():
            walk(value, path + '.' + str(key))
    elif isinstance(node, list):
        for i, value in enumerate(node):
            walk(value, path + '.' + str(i))
for name, gate in gates.items():
    walk(gate, name)
expected_falsifiers = {
    'exchange.json.literal_W_difference.false_tail_omitted',
    'exchange.json.false_direction_ignored', 'exchange.json.false_parent_coverage',
    'exchange.json.false_bare_downward_pair_nonpositive',
    'operator.json.false_small_commutator_promotion',
    'operator.json.false_oriented_mass_equals_symmetrization',
    'operator.json.false_full_H_positive_semidefinite',
    'operator.json.false_theta_substituted_for_raw_on_long_edge',
}
assert set(falsifiers) == expected_falsifiers
exchange, operator = gates['exchange.json'], gates['operator.json']
assert exchange['M'] == 1000000
assert set(exchange['exchanges']) == {'minus_two_joint', 'plus_two_joint', 'minus_two_unmatched_parent'}
down = exchange['exchanges']['minus_two_joint']
assert (down['m0'], down['m1'], down['n0'], down['n1']) == (33584829, 33564027, 66415171, 66435973)
assert down['principal_S_sign']['sign'] == down['principal_constant_sign']['sign'] == 'NEGATIVE'
assert down['whole_sign']['sign'] == 'POSITIVE'
assert down['first']['U_a'] == {'3': '-1'} and down['second']['U_a'] == {'3': '1'}
assert down['first']['U_alpha'] == {'3': '-1'} and down['second']['U_alpha'] == {}
assert down['first']['U_band_alpha_a'] == {} and down['second']['U_band_alpha_a'] == {'3': '1'}
for pair in exchange['exchanges'].values():
    assert pair['source_onset_not_assumed_at_finite_N'] is True
    assert pair['large_factor_kernel_changed'] is True and pair['incomplete_small_fibre_retained'] is True
    assert pair['first']['all_k_equals_ge2'] is True and pair['second']['all_k_equals_ge2'] is True
assert exchange['exchanges']['plus_two_joint']['principal_S_sign']['sign'] == 'POSITIVE'
assert exchange['exchanges']['minus_two_unmatched_parent']['second']['theta'] == {}
variation = exchange['literal_W_difference']
assert variation['status'] == 'PASS_NEW_LITERAL_TWO_FRONT_W_IDENTITY_ONLY'
assert variation['front_formula'] == 'min(Q,(m-1)//a)' and (variation['R0'], variation['R1']) == (10618, 10611)
assert variation['k1_included'] is True
assert variation['actual_difference'] == variation['identity_difference']
assert variation['analytical_variation_bound_numerically_tested'] is False
assert [(t['k'], t['coefficient']) for t in variation['tail_terms']] == [(10613, '-1/10612'), (10617, '1/7076')]
assert variation['false_tail_omitted']['sign']['sign'] == 'NEGATIVE'
small, long = operator['complete_cubes']['small'], operator['complete_cubes']['raw_long']
assert len(small['vertices']) == 8 and small['edge_count'] == 12
assert len(long['vertices']) == 16 and long['edge_count'] == 32
assert small['active_raw_vertices'] == [11, 561]
assert small['signed_symmetric_J_Qphys_ones'] == {} and small['oriented_J_TV_ones']
for cube in (small, long):
    for key in ('complete_cube', 'actual_matching_is_S_cN', 'matching_not_replaced_by_constant',
                'global_c_long_complement_not_discarded', 'reference_minus_S_N_N_retained_outside_selected_cube',
                'raw_properpowers_not_masked'):
        assert cube[key] is True
    assert all(e['orientations_T_and_Tstar_retained'] and e['parity_anticommutation'] for e in cube['edges'])
assert operator['false_small_commutator_promotion']['sign']['sign'] == 'POSITIVE'
assert operator['false_full_H_positive_semidefinite']['sign']['sign'] == 'NEGATIVE'
assert long['nodes']['35727711']['raw'] == {'8017': '1'} and long['nodes']['35727711']['theta'] == {}
assert operator['false_theta_substituted_for_raw_on_long_edge']['theta_numerator'] == {}
numeric_audit = dict(status='PASS_READ_ONLY_FROZEN_REPLAY_AUDIT', banks=bank_audits,
    numerical_manifest_sha256=sha(ROUND / 'numeric_manifest.json'),
    original_replay_receipt_sha256=sha(ROUND / 'numerical_replay.json'),
    producer_repeated_by_judge=False, falsifiers=falsifiers, falsifier_count=len(falsifiers),
    rational_signs=signs, rational_sign_count=len(signs), strict_signs=True, floating_values=0,
    asymptotic_tested=False, analytic_payment_tested=False, source_onset_tested=False)
write_json(JUDGE / 'numerical_audit_receipt.json', numeric_audit)

# No compilation is entered until the final numerical inputs have passed the read-only audit.
helper = JUDGE / 'lean-audit.py'
spec = importlib.util.spec_from_file_location('goldbach_round13_judge_lean', helper)
assert spec is not None and spec.loader is not None
lean = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lean)
lean_audit = lean.run(inputs, JUDGE, BASE)
verify_inputs()
after = preservation()
assert before == after
receipt = dict(round=13, status='PARTIAL_ACTUAL_PRIME_SEMIPRIME_SWITCH_WITH_UNPAID_COMPLEMENT',
    recorded_at_utc=datetime.now(timezone.utc).isoformat(), input_manifest=str(MANIFEST),
    input_manifest_sha256=sha(MANIFEST), input_sha256=inputs['sha256'], external_sha256=inputs['external_sha256'],
    final_role_signals=inputs['final_role_signals'], numerical_audit=numeric_audit,
    numerical_audit_receipt_sha256=sha(JUDGE / 'numerical_audit_receipt.json'),
    preservation_before=before, preservation_after=after,
    previous_auxiliary_modules=13, previous_auxiliary_conclusions=169, **lean_audit,
    written_switch_payment=dict(amount='21*N^(31/32)*u^2', subset='actually matched admissible tuples only',
        elementary_derivation_u_min=16, ledger_source_u_min='10^24', written_not_compiler_certified=True,
        paired_fee_only=True, unmatched_not_assumed_small=True, P5_full_bulk_J2_preserved=True),
    semantic_open_obligations=['Coverage and unmatched physical J0/J1/J2 remain unestimated',
        'Signed B13 operator and matching S(cN), c=1, -S(N)N and c>a remain unpaid',
        'H2, singleton and face terms remain in their complete principal model',
        'Physical-band BV extra effective onset and covered 2 max(e,0) remain unpaid'],
    old_banks_rerun=False, old_independent_modules_rerun=False, required_old_dependencies_rebuilt=True,
    custom_oleans_reused=False, source_adaptive_u_min='10^24', finite_N=100000000,
    global_no_go=False, victory=False, score=0,
    judge_scripts_sha256={n: sha(JUDGE / n) for n in ('audit-judge.ps1', 'freeze-inputs.py', 'run-audit.py', 'lean-audit.py')})
write_json(JUDGE / 'judge_receipt.json', receipt)
print(json.dumps(dict(status=receipt['status'], preserved=514, bank_copies_audited=2,
    falsifiers=len(falsifiers), rational_signs=len(signs), lean_exit_codes=[r['exit_code'] for r in lean_audit['dependency_rebuilds']+lean_audit['modules']],
    new_theorems=lean_audit['new_lean_conclusions'], cumulative_theorems=lean_audit['cumulative_auxiliary_conclusions'],
    victory=False, score=0), indent=2))
