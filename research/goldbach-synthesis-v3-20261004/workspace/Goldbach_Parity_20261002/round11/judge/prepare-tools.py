"""Adapt the previously verified judge driver as source text; execute no old bank."""
from pathlib import Path

JUDGE = Path(__file__).resolve().parent
ROUND = JUDGE.parent
PREVIOUS = ROUND.parent / 'round10' / 'judge'
OLD_REGISTRY = '39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb'
NEW_REGISTRY = 'f86a31f72d624124338afad6932cd859dceae164a6f3422f9b8998164fcf9e05'

ps = (PREVIOUS / 'verify-frozen.ps1').read_text(encoding='utf-8')
ps = ps.replace('round10', 'current_round_temp').replace('round9', 'round10').replace('current_round_temp', 'round11')
ps = ps.replace('341', '405').replace(OLD_REGISTRY, NEW_REGISTRY)
(JUDGE / 'verify-frozen.ps1').write_text(ps, encoding='utf-8')
ps = (PREVIOUS / 'audit-judge.ps1').read_text(encoding='utf-8').replace('round10', 'round11').replace('Round10', 'Round11').replace('341', '405')
(JUDGE / 'audit-judge.ps1').write_text(ps, encoding='utf-8')
driver = (PREVIOUS / 'run-judge.py').read_text(encoding='utf-8')
driver = driver.replace('round10', 'round11').replace(OLD_REGISTRY, NEW_REGISTRY)
driver = driver.replace('== 341', '== 405')
start = driver.index("output = JUDGE / 'numerical'")
end = driver.index('def executable_lean(text):')
numeric = '''output = JUDGE / 'numerical'
output.mkdir(exist_ok=True)
for script in ['contract_witnesses.py', 'ap_prefix_checks.py', 'paired_axes_checks.py']:
    source = ROUND / script
    shutil.copyfile(source, output / script)
    argv = sys.argv
    sys.argv = [str(source), '--output-dir', str(output)]
    try:
        with (output / (source.stem + '.log')).open('w', encoding='utf-8') as log:
            with contextlib.redirect_stdout(log):
                runpy.run_path(str(source), run_name='__main__')
    finally:
        sys.argv = argv

numeric = {}
gates = {}
expected_status = {'witnesses.json': 'VERIFIED_NEW_FINITE_WITNESSES_ONLY',
    'ap_prefix.json': 'PASS_NEW_FINITE_CONTRACTS_ONLY',
    'paired_axes.json': 'PASS_NEW_PAIR_IDENTITY_ONLY'}
for name in expected_status:
    original, replay = ROUND / name, output / name
    production = json.loads(original.read_text(encoding='utf-8'))
    reproduced = json.loads(replay.read_text(encoding='utf-8'))
    assert production == reproduced, name
    assert original.read_bytes() == replay.read_bytes(), name
    assert reproduced['N'] == 100000000 and reproduced['status'] == expected_status[name]
    assert not any(reproduced[key] for key in ['global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory'])
    for key in ['properpowers_removed_from_raw', 'mu_n_squared_added', 'principal_substituted_for_actual_kernels', 'global_no_go']:
        assert reproduced.get(key, False) is False
    for relative, expected in reproduced['imports'].items():
        assert sha(BASE / relative) == expected, relative
    assert reproduced['conservation_before']['files'] == reproduced['conservation_after']['files'] == 405
    numeric[name] = dict(all_fields_equal=True, all_bytes_equal=True,
        production_sha256=sha(original), replay_sha256=sha(replay), status=reproduced['status'])
    gates[name] = reproduced

assert gates['witnesses.json']['script_sha256'] == sha(ROUND / 'contract_witnesses.py')
for name, script in [('ap_prefix.json', 'ap_prefix_checks.py'), ('paired_axes.json', 'paired_axes_checks.py')]:
    gate = gates[name]
    assert gate['script_sha256'] == sha(ROUND / script)
    assert gate['witness_script_sha256'] == sha(ROUND / 'contract_witnesses.py')
    assert gate['exact_helper_sha256'] == sha(ROUND / 'exact11.py')
    assert gate['shared_sha256'] == sha(ROUND / 'shared.py')

ap, paired = gates['ap_prefix.json'], gates['paired_axes.json']
assert ap['finite_coefficients']['status'] == 'PASS_FINITE_LOCAL_IDENTITY_ONLY'
assert ap['finite_coefficients']['B6_guarded_finite_product']['status'] == 'PASS_IDENTITY_ONLY'
assert ap['prefix_expansion']['status'] == 'PASS_IDENTITY_ONLY_WITH_RESTRICTED_E'
assert ap['scope_and_reference']['status'] == 'DISTINCT_LOW_PREFIX_AND_BAND_VERIFIED'
assert len(ap['finite_coefficients']['B6_guarded_finite_product']['all_divisors']) == 16
assert len(ap['prefix_expansion']['records']) == 12
assert len(ap['prefix_expansion']['prime_E']) == 5
assert not ap['finite_coefficients']['infinite_tail_evaluated']
assert ap['scope_and_reference']['false_pointwise_G_nonnegative']['G_over_S_N'] == '-1'
assert ap['properpower_first_axis']['n'] == 9
falsifiers = {}
certificates = {}
def inspect_contract(node, path):
    if isinstance(node, dict):
        if node.get('status') == 'ERROR_FALSIFIER':
            falsifiers[path] = node['status']
        if 'sign' in node and 'lower' in node and 'upper' in node:
            sign = node['sign']
            lo, hi = Fraction(node['lower']), Fraction(node['upper'])
            assert lo <= hi
            assert sign in {'NEGATIVE', 'POSITIVE', 'ZERO'}, (path, sign)
            if sign == 'NEGATIVE': assert hi < 0
            if sign == 'POSITIVE': assert lo > 0
            if sign == 'ZERO': assert lo == hi == 0
            certificates[path] = sign
        for key, value in node.items():
            inspect_contract(value, path + '.' + key)
    elif isinstance(node, list):
        for i, value in enumerate(node): inspect_contract(value, path + '[' + str(i) + ']')
for name, gate in gates.items(): inspect_contract(gate, name)
expected_falsifiers = {
    'ap_prefix.json.finite_coefficients.nonunit_r5',
    'ap_prefix.json.finite_coefficients.nonsquarefree_r9',
    'ap_prefix.json.finite_coefficients.intersection',
    'ap_prefix.json.prefix_expansion.omitted_tail',
    'ap_prefix.json.prefix_expansion.actual_intersection',
    'ap_prefix.json.scope_and_reference.rows.low_prefix',
    'ap_prefix.json.scope_and_reference.rows.low_plus_band',
    'ap_prefix.json.scope_and_reference.rows.negative_reference',
    'ap_prefix.json.scope_and_reference.false_pointwise_G_nonnegative',
    'ap_prefix.json.properpower_first_axis',
    'paired_axes.json.false_pair_favorable',
    'paired_axes.json.incidence_defect',
    'paired_axes.json.missing_face',
}
assert set(falsifiers) == expected_falsifiers, falsifiers
assert paired['pairs']['both_prime']['pair_sign']['sign'] == 'POSITIVE'
assert paired['pairs']['both_prime']['principal_sign']['sign'] == 'NEGATIVE'
assert paired['pairs']['one_prime_axis']['principal_sign']['sign'] == 'POSITIVE'
assert paired['incidence_defect']['incorrect_sign']['sign'] == 'NEGATIVE'
assert paired['missing_face']['tripled_n'] < 0
assert len(paired['full_partitions']) == 2
for partition in paired['full_partitions'].values():
    assert partition['status'] == 'PASS_FULL_FINITE_PARTITION_AND_P2_ONLY'
    assert partition['X_t'] == [1, 3, 7] and partition['D_t'] == [1] and partition['F_t'] == [7]
    assert partition['three_D_t'] == [3] and partition['disjoint_partition'] is True
    assert partition['positive_common_mu_negative_bases'] == []
    assert partition['positive_common_asymptotic_budget_numerically_validated'] is False
    assert partition['S_N_not_evaluated'] is True and partition['actual_kernels_not_replaced'] is True
verify_inputs()
assert snapshot() == before
numeric_receipt = dict(status='PASS_EXACT_REPLAY', jsons=numeric,
    contract_statuses={name: gates[name]['status'] for name in gates},
    falsifiers=falsifiers, falsifier_count=len(falsifiers),
    strict_rational_signs_checked=True, sign_certificate_count=len(certificates),
    sign_certificates=certificates, finite_domain_N=100000000,
    B6_divisor_cases=16, AP_cut_cases=12, restricted_prime_E_count=5,
    three_adic_partitions=2, old_banks_replayed=False,
    analytical_payments_tested=False, global_D_N_estimated=False, victory=False)
write_json(output / 'replay_receipt.json', numeric_receipt)

'''
driver = driver[:start] + numeric + driver[end:]
driver = driver.replace("for relative in inputs['new_lean_sources']:",
    "source_jobs = [(Path(p), False) for p in inputs['dependency_sources']] + [(ROUND / p, True) for p in inputs['new_lean_sources']]\nfor original, is_new in source_jobs:\n    relative = str(original)")
driver = driver.replace("    original = ROUND / relative\n    original_text", "    original_text")
driver = driver.replace("entry = dict(module=original.stem, original_source_sha256=sha(original),",
    "entry = dict(module=original.stem, new_module=is_new, original_source_sha256=sha(original),")
driver = driver.replace("new_count = sum(row['theorem_count'] for row in lean_results)",
    "new_results = [row for row in lean_results if row['new_module']]\ndependency_results = [row for row in lean_results if not row['new_module']]\nnew_count = sum(row['theorem_count'] for row in new_results)\nassert len(new_results) == 2 and len(dependency_results) == 1\nassert dependency_results[0]['theorem_count'] == 17")
driver = driver.replace('round=10,', 'round=11,')
driver = driver.replace('PARTIAL_NATIVE_COFACTOR_IDENTITIES_WITH_OPEN_SIGNED_COMPENSATION', 'PARTIAL_COMMON_MODEL_COMPENSATION_WITH_RETAINED_SINGLETONS_FACES_AND_ENTROPY')
driver = driver.replace('new_lean_modules=len(lean_results)', 'new_lean_modules=len(new_results)')
driver = driver.replace('previous_auxiliary_modules=9, previous_auxiliary_conclusions=116', 'previous_auxiliary_modules=11, previous_auxiliary_conclusions=141')
driver = driver.replace('cumulative_auxiliary_modules=9+len(lean_results), cumulative_auxiliary_conclusions=116+new_count', 'cumulative_auxiliary_modules=11+len(new_results), cumulative_auxiliary_conclusions=141+new_count')
driver = driver.replace("modules=lean_results,", "modules=new_results, dependency_rebuilds=dependency_results,")
driver = driver.replace("'H2-S(N)M2, J0/J1 and E11/E12 remain unpaid'", "'P6 retains H2, singletons, faces, entropy, J0/J1 and the true detector; B13 remains unpaid'")
driver = driver.replace("'Written corner and singular-mask payments do not replace parity compensation'", "'Written P5 pays the common model alone when 3 is coprime to N; it does not pay the whole pair'")
driver = driver.replace('old_lean_modules_recompiled=False', 'old_independent_lean_modules_recompiled=False, required_old_dependency_rebuilt=True')
driver = driver.replace('cumulative_theorems=116+new_count, preserved_files=341', 'cumulative_theorems=141+new_count, dependency_theorems=17, preserved_files=405')
(JUDGE / 'run-judge.py').write_text(driver, encoding='utf-8')
print('Judge11 tools prepared as source only; no bank, compiler, manifest freeze or verdict executed.')
