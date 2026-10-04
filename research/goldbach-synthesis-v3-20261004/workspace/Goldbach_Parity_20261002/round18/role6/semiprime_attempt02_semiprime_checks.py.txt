"""Selected new double-semiprime extraction: complete closed q window and physical union."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from pathlib import Path
from fractions import Fraction
from math import gcd
import argparse
import json
sys.path.insert(0, str(Path(__file__).resolve().parent / 'role6'))
import strict as s
import semiprime_helpers as h

ROOT = Path(__file__).resolve().parent
REPORT_SHA = '48dbcc5875c140d6d4991fa7d6cd58749048e3cf151e35f476893c27f81ae595'
REGISTRY_SHA = '05212665afffecade91134e1533f93d11eba8058179198e4420eef1fe252f2bc'
STRICT_SHA = '20aada21669af3869b1ef1fee4b0e846cbc64b543e765fbf1943dcc8f2825a8a'
P0, Z, QLOW, QHIGH, T, Y = 3, 100, 1400100, 1405100, 3, 1


def axis(n):
    f = s.factor(n)
    unit = gcd(n, s.N) == 1
    theta = n if unit and f == ((n, 1),) else None
    raw = f[0][0] if unit and len(f) == 1 else None
    return {'n': n, 'factorization': f, 'unit_N': unit,
            'theta_log_base': theta, 'raw_Lambda_log_base': raw,
            'proper_power': bool(len(f) == 1 and f[0][1] > 1)}


def semiprime_resource(data):
    n, f = data['n'], data['factorization']
    ell = f[0][0]
    quotient = n // ell
    selected = ell <= Z and s.prime(quotient)
    return {'least_prime_factor': ell, 'quotient': quotient,
            'quotient_factorization': s.factor(quotient), 'quotient_prime': s.prime(quotient),
            'canonical_small_semiprime': selected}


def switch_record(e, ell1, ell0):
    assert ell1 != ell0 and ell0 != P0 and ell1 >= P0 and ell0 >= P0
    L = ell1 * ell0
    a1, a0 = s.N % ell1, s.N * pow(P0, -1, ell0) % ell0
    A = a1 + ell1 * ((a0 - a1) * pow(ell1, -1, ell0) % ell0)
    assert 0 <= A < L and (A - s.N) % ell1 == 0 and (P0 * A - s.N) % ell0 == 0
    assert gcd(A, L) == 1
    assert (s.N - A) % ell1 == 0 and (s.N - P0 * A) % ell0 == 0
    forms = [(L, A), (-e * L, s.N - e * A),
             (-ell0, (s.N - A) // ell1), (-P0 * ell1, (s.N - P0 * A) // ell0)]
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    determinants = [forms[i][0] * forms[j][1] - forms[j][0] * forms[i][1] for i, j in pairs]
    expected = [s.N * L, s.N * ell0, s.N * ell1,
                s.N * ell0 * (1 - e), s.N * ell1 * (P0 - e), s.N * (P0 - 1)]
    assert determinants == expected
    slope_product = s.product(form[0] for form in forms)
    assert slope_product == -e * P0 * L ** 3
    delta = abs(slope_product * s.product(determinants))
    formula_delta = s.N ** 6 * e * P0 * L ** 6 * (e - 1) * (e - P0) * (P0 - 1)
    assert delta == formula_delta > 0 and delta <= s.N ** 11 and delta ** 4 <= s.N ** 41
    radical = s.rad_components(s.N, e, P0, L, e - 1, e - P0, P0 - 1)
    guard1, guard0 = e % ell1 != 1, e % ell0 != P0 % ell0
    guarded = guard1 and guard0
    primitive_gcds = [gcd(abs(a), abs(b)) for a, b in forms]
    if guarded:
        assert primitive_gcds == [1, 1, 1, 1]
    roots_catalog, rho, saturation = {}, {}, []
    for p in [v for v in s.PRIMES if v <= Z]:
        roots = [x for x in range(p) if h.product_form(forms, x) % p == 0]
        rho[p] = len(roots)
        good = delta % p != 0
        if guarded:
            assert 1 <= len(roots) <= min(4, p)
            if p in (ell1, ell0):
                assert len(roots) == 1
            if good:
                assert len(roots) == 4
        if len(roots) == p:
            saturation.append(p)
        roots_catalog[str(p)] = {'roots': roots, 'rho': len(roots), 'outside_delta_switch': good}
    maxq = (s.N - s.Q - 1) // e
    source_low, source_high = s.ceildiv(s.M - A, L), (maxq - A) // L
    full_count = max(0, source_high - source_low + 1)
    source_bound = Fraction(s.N, e * L) + 1
    assert full_count <= source_bound
    low, high = s.ceildiv(QLOW - A, L), (QHIGH - A) // L
    local_count = max(0, high - low + 1)
    assert local_count <= Fraction(QHIGH - QLOW + 1, L) + 1
    assert source_low <= low <= high <= source_high
    return {'e': e, 'ell1': ell1, 'ell0': ell0, 'L': L, 'A': A,
            'CRT_inverses': {'p0_inverse_mod_ell0': pow(P0, -1, ell0),
                             'ell1_inverse_mod_ell0': pow(ell1, -1, ell0)},
            'forms_order': ['q', 'n_e', 'r1', 'r0'], 'slope_constant_pairs': forms,
            'oriented_determinants_order': ['12', '13', '14', '23', '24', '34'],
            'oriented_determinants': determinants, 'D3_exact': True,
            'slope_product': slope_product, 'Delta_switch': str(delta),
            'radical_switch_equals_radical_Delta_e_L': radical, 'D4_exact': True,
            'target_guards': {'e_not1_mod_ell1': guard1, 'e_notp0_mod_ell0': guard0,
                              'both': guarded}, 'primitive_gcds': primitive_gcds,
            'rho_actual_primes_through100': roots_catalog, 'saturated_primes': saturation,
            'source_q_range': [s.M, maxq], 'source_x_range': [source_low, source_high],
            'source_x_count': full_count, 'D2_outer_plus1_upper_exact': str(source_bound),
            'finite_q_window': [QLOW, QHIGH], 'finite_x_range': [low, high],
            'finite_x_count': local_count, 'finite_outer_plus1_kept': True,
            'Selberg_T3': h.local_selberg(forms, low, high, rho, T),
            'source_logarithmic_estimates_D5_D10_D11_not_applied': True}


def run():
    assert s.digest(ROOT / 'agent2_capacity_incidence.md') == REPORT_SHA
    assert s.digest(ROOT / 'previous_artifacts_sha256.json') == REGISTRY_SHA
    assert s.digest(ROOT / 'role6' / 'strict.py') == STRICT_SHA
    assert s.N % 2 == 0 and s.N % P0 and all(s.N % p == 0 for p in (2,) if p < P0)
    assert s.prime(P0) and P0 <= Z and Z ** 4 <= s.N < (Z + 1) ** 4
    assert T ** 16 <= s.N < (T + 1) ** 16 and Y ** 32 <= T < (Y + 1) ** 32
    assert QHIGH - QLOW + 1 == 5001 and QLOW >= s.M
    allcores = [e for e in range(P0 + 1, 71) if h.mu(e) and gcd(e, s.N) == 1]
    core_info = [{'e': e, 'factorization': s.factor(e), 'mu_e': h.mu(e),
                  'Lambda_e': h.serialize(h.Lambda(e)), 'prime': s.prime(e)} for e in allcores]
    primes_q, q_catalog, switches, physical = [], [], {}, {}
    counts = {'A': 0, 'R': 0, 'S': 0, 'SS': 0, 'S_minus_SS': 0}
    raw_target_catalog, resource_pp, unpaid_witnesses = [], [], []
    excluded_classes_raw = []
    def physical_role(m, role, label):
        row = physical.setdefault(m, {'m': m, 'first_axis_n': s.N - m, 'roles': [], 'labels': []})
        if role not in row['roles']:
            row['roles'].append(role)
        if label not in row['labels']:
            row['labels'].append(label)
    for q in range(QLOW, QHIGH + 1):
        assert (s.N - s.Q - 1) // q == 70
        if not s.prime(q) or gcd(q, s.N) != 1:
            continue
        primes_q.append(q)
        n1, n0 = axis(s.N - q), axis(s.N - P0 * q)
        r1, r0 = semiprime_resource(n1), semiprime_resource(n0)
        if n1['proper_power'] or n0['proper_power']:
            resource_pp.append({'q': q, 'n1': n1, 'n0': n0})
        if n1['theta_log_base'] or n0['theta_log_base']:
            partition = 'A'
        elif r1['least_prime_factor'] > Z and r0['least_prime_factor'] > Z:
            partition = 'R'
        else:
            partition = 'S'
        SS = r1['canonical_small_semiprime'] and r0['canonical_small_semiprime']
        ell1, ell0 = r1['least_prime_factor'], r0['least_prime_factor']
        if SS:
            assert partition == 'S' and ell1 != ell0 and ell0 != P0
            assert ell1 >= P0 and ell0 >= P0
            assert r1['quotient'] > ell1 and r0['quotient'] > ell0
            assert r1['quotient'] > s.A and r0['quotient'] > s.A
            assert r1['quotient'] >= s.M and r0['quotient'] ** 2 >= s.N
            physical_role(n1['n'], 'reciprocal_m1_existing_resource', f'q={q}')
            physical_role(n0['n'], 'reciprocal_m0_zero_raw_axis', f'q={q}')
            assert axis(P0 * q)['raw_Lambda_log_base'] is None
        rows = []
        for e in allcores:
            m, ne = e * q, s.N - e * q
            target = axis(ne)
            assert ne > s.Q and m <= s.N - s.Q - 1 and gcd(m, s.N) == 1
            assert h.mu(m) == -h.mu(e) and not h.Lambda(m)
            assert h.prefix(m, s.A) == s.scaled(h.Lambda(e), -1)
            demand = target['theta_log_base'] is not None
            row = {'e': e, 'm': m, 'target_axis': target, 'mu_e': h.mu(e),
                   'mu_m': h.mu(m), 'Lambda_e': h.serialize(h.Lambda(e)),
                   'whole_U_a_equals_negative_Lambda_e': True,
                   'theta_demand': demand, 'resource_partition': partition, 'SS_resources': SS}
            if demand:
                counts[partition] += 1
                if partition == 'S':
                    counts['SS' if SS else 'S_minus_SS'] += 1
                if partition == 'S' and not SS and len(unpaid_witnesses) < 8:
                    unpaid_witnesses.append({'q': q, 'e': e, 'm': m, 'n_e': ne,
                                            'n1_factorization': n1['factorization'], 'n0_factorization': n0['factorization'],
                                            'support_SS_equals_S_false': True, 'debt_coefficient_uncomputed_not_presumed_positive': True})
            if target['proper_power']:
                raw_target_catalog.append({'q': q, 'e': e, 'target_axis': target, 'SS_resources': SS})
            if SS:
                switch_key = f'{e}:{ell1}:{ell0}'
                if switch_key not in switches:
                    switches[switch_key] = switch_record(e, ell1, ell0)
                switch = switches[switch_key]
                assert (q - switch['A']) % switch['L'] == 0
                x = (q - switch['A']) // switch['L']
                expected = [q, ne, r1['quotient'], r0['quotient']]
                actual = [h.eval_form(form, x) for form in switch['slope_constant_pairs']]
                assert actual == expected
                row['switch_ref'] = switch_key
                row['actual_x'] = x
                row['actual_divided_form_values'] = actual
                guarded = switch['target_guards']['both']
                if not guarded:
                    assert not demand
                    if target['raw_Lambda_log_base']:
                        excluded_classes_raw.append({'q': q, 'e': e, 'target_axis': target, 'switch_ref': switch_key})
                if demand:
                    assert guarded and not switch['saturated_primes']
                    assert all(value > Z and s.prime(value) for value in actual)
                    physical_role(m, 'SS_theta_demand', f'q={q},e={e}')
                elif target['raw_Lambda_log_base']:
                    physical_role(m, 'SS_raw_proper_power_axis', f'q={q},e={e}')
                if target['raw_Lambda_log_base']:
                    row['kernel_ref'] = str(m)
                    row['kernel_status'] = 'NEW_SELECTED_NONZERO_RAW_AXIS'
                else:
                    row['kernel_status'] = 'LITERAL_UNEVALUATED_ZERO_RAW_AXIS'
                    row['literal_weighted_term'] = '0'
            else:
                row['kernel_status'] = 'UNPAID_LITERAL_OUTSIDE_SS' if target['raw_Lambda_log_base'] else 'LITERAL_UNEVALUATED_ZERO_RAW_AXIS'
                if not target['raw_Lambda_log_base']:
                    row['literal_weighted_term'] = '0'
            rows.append(row)
        q_catalog.append({'q': q, 'q_factorization': s.factor(q), 'core_cap': 70,
                          'n1_axis': n1, 'n0_axis': n0, 'n1_canonical_factor': r1, 'n0_canonical_factor': r0,
                          'resource_partition': partition, 'SS_resources': SS,
                          'all_core_rows': rows, 'reciprocal_m1_anchor_p0_already_present': bool(SS and ell1 == P0)})
    assert counts['S'] == counts['SS'] + counts['S_minus_SS']
    assert counts['A'] + counts['R'] + counts['S'] == sum(row['theta_demand'] for qrow in q_catalog for row in qrow['all_core_rows'])
    selected_active = sorted(m for m, row in physical.items() if axis(s.N - m)['raw_Lambda_log_base'])
    zero_vertices = sorted(m for m, row in physical.items() if not axis(s.N - m)['raw_Lambda_log_base'])
    assert all('reciprocal_m0_zero_raw_axis' in physical[m]['roles'] for m in zero_vertices)
    max_cutoff = max([min(s.Q, (m - 1) // s.A) for m in selected_active] + [1])
    print(json.dumps({'stage': 'complete_new_window_and_divided_forms', 'all_q_integers': 5001,
                      'prime_unit_q': len(primes_q), 'cores': len(allcores), 'partition_counts': counts,
                      'SS_resource_q': sum(q['SS_resources'] for q in q_catalog),
                      'switch_triplets': len(switches), 'new_active_physical_vertices': len(selected_active),
                      'literal_zero_physical_vertices': len(zero_vertices), 'short_table_cap': max_cutoff}), flush=True)
    h.prepare_short_tables(max_cutoff)
    kernels, polynomials, selected_theta, selected_rawpp = {}, {}, {}, {}
    debt_SS, signed_SS, raw_SS, capacity_unique, physical_signed = {}, {}, {}, {}, {}
    coefficient_mu_counts = {'-1': 0, '1': 0, '0': 0}
    resources = []
    for index, m in enumerate(selected_active):
        record, C, W = h.kernel(m)
        data = physical[m]
        first = axis(s.N - m)
        raw_vector = {first['raw_Lambda_log_base']: Fraction(1)}
        weighted = h.multiply(raw_vector, C)
        polynomials[m] = weighted
        weighted_certificate = h.polynomial_certificate(weighted)
        record['first_axis_raw'] = first
        record['weighted_raw_C_sign_certificate'] = weighted_certificate
        record['C_sign_certificate'] = s.vector_certificate(C)
        record['W_kernel_sign_certificate'] = s.vector_certificate(W)
        roles = data['roles']
        if 'SS_theta_demand' in roles:
            assert first['theta_log_base']
            h.poly_add(signed_SS, weighted)
            if weighted_certificate['sign'] == 'POSITIVE':
                h.poly_add(debt_SS, weighted)
            selected_theta[str(m)] = {'q_e_labels': data['labels'],
                                      'raw_equals_theta': True, 'sign_certificate': weighted_certificate,
                                      'positive_part_retained': weighted_certificate['sign'] == 'POSITIVE'}
        if 'SS_raw_proper_power_axis' in roles:
            assert first['proper_power'] and not first['theta_log_base']
            h.poly_add(raw_SS, weighted)
            h.poly_add(selected_rawpp, weighted)
        if 'reciprocal_m1_existing_resource' in roles:
            f = s.factor(m)
            assert len(f) == 2 and all(exponent == 1 for _, exponent in f)
            ell, r = f[0][0], f[1][0]
            assert ell <= Z < s.A < r and r >= s.M and first['theta_log_base']
            assert [d for d in h.divisors(m) if d <= s.A] == [1, ell]
            expected_C = {ell: Fraction(1)}
            s.add(expected_C, W)
            assert C == expected_C
            if weighted_certificate['sign'] == 'NEGATIVE':
                h.poly_add(capacity_unique, weighted, -1)
            resources.append({'m1': m, 'first_axis_q': s.N - m, 'ell1': ell, 'r1': r,
                              'short_divisors_le_a': [1, ell], 'C_equals_log_ell_plus_actual_W': True,
                              'already_p0_anchor_vertex': ell == P0,
                              'anchor_large_prime_label_if_present': r if ell == P0 else None,
                              'capacity_positive_part_sign_certificate': h.polynomial_certificate(
                                  {key: -value for key, value in weighted.items()} if weighted_certificate['sign'] == 'NEGATIVE' else {}),
                              'counted_once_not_per_e': True, 'not_new_credit_if_already_anchor': True})
        h.poly_add(physical_signed, weighted)
        coefficient_mu_counts[str(record['mu_m'])] += 1
        kernels[str(m)] = record
        data['kernel_ref'] = str(m)
        data['kernel_status'] = 'NEW_SELECTED_KERNEL_EVALUATED_ONCE'
        if index % 5 == 0 or index + 1 == len(selected_active):
            print(json.dumps({'stage': 'new_selected_kernels', 'done': index + 1, 'total': len(selected_active), 'm': m}), flush=True)
    for m in zero_vertices:
        physical[m]['kernel_status'] = 'LITERAL_UNEVALUATED_EXACT_ZERO_RAW_AXIS'
        physical[m]['literal_weighted_term'] = '0'
        first = axis(s.N - m)
        assert first['factorization'] == ((P0, 1), ((s.N - m) // P0, 1))
        assert first['raw_Lambda_log_base'] is None and first['theta_log_base'] is None
    # Gather strict local falsifiers. None asserts a global inability or a source-onset result.
    falsifiers = []
    falsifiers.append({'promotion': 'SS=S entire support',
                       'status': 'LOCAL_SUPPORT_PROMOTION_FALSIFIED' if unpaid_witnesses else 'NO_COUNTEREXAMPLE',
                       'witnesses': unpaid_witnesses, 'uncomputed_debt_sign_not_inferred': True, 'no_global_impossibility': True})
    m0witnesses = [{'m0': m, 'first_axis_3q': s.N - m, 'factorization': s.factor(s.N - m),
                    'raw_Lambda_N_exact': '0'} for m in zero_vertices[:8]]
    falsifiers.append({'promotion': 'reciprocal_j=p0 gives nonzero raw capacity',
                       'status': 'LOCAL_PROMOTION_FALSIFIED' if m0witnesses else 'NO_COUNTEREXAMPLE',
                       'witnesses': m0witnesses, 'no_global_impossibility': True})
    four_rho_witnesses, primitive_witnesses = [], []
    for k, rec in switches.items():
        if rec['target_guards']['both'] and len(four_rho_witnesses) < 8:
            p = rec['ell1']
            actual_rho = rec['rho_actual_primes_through100'][str(p)]['rho']
            assert actual_rho == 1
            four_rho_witnesses.append({'switch_ref': k, 'prime_witness': p, 'rho_actual': actual_rho})
        if not rec['target_guards']['both'] and rec['primitive_gcds'][1] > 1 and len(primitive_witnesses) < 8:
            primitive_witnesses.append({'switch_ref': k, 'target_guards': rec['target_guards'],
                                        'gcd_of_n_e_slope_and_constant': rec['primitive_gcds'][1]})
    falsifiers.append({'promotion': 'rho=4 on primes dividing witness conductor L',
                       'status': 'LOCAL_PROMOTION_FALSIFIED' if four_rho_witnesses else 'NO_COUNTEREXAMPLE',
                       'witnesses': four_rho_witnesses, 'no_global_impossibility': True})
    falsifiers.append({'promotion': 'n_e divided form primitive without target exclusions',
                       'status': 'LOCAL_PROMOTION_FALSIFIED' if primitive_witnesses else 'NO_COUNTEREXAMPLE',
                       'witnesses': primitive_witnesses, 'no_global_impossibility': True})
    partial_deficit = dict(debt_SS)
    h.poly_add(partial_deficit, capacity_unique, -1)
    referenced_kernels = {str(m) for m in selected_active}
    assert referenced_kernels == set(kernels)
    all_axes_rows = sum(len(q['all_core_rows']) for q in q_catalog)
    result = {
        'status': 'PASS_NEW_DOUBLE_SEMIPRIME_DIVIDED_FORMS_AND_PHYSICAL_UNION',
        'round': 18, 'contract_FINAL2_sha256': REPORT_SHA, 'protected_registry_sha256': REGISTRY_SHA,
        'N': s.N, 'p0_actual_least_missing_odd_prime_finite': P0, 'Z': Z,
        'alpha': s.ALPHA, 'a': s.A, 'Q': s.Q, 'M': s.M, 'T_finite': T, 'Y_finite': Y,
        'complete_window': {'q_low': QLOW, 'q_high': QHIGH, 'integer_count': 5001,
                            'q_factorizations_complete_column': s.factor_column(range(QLOW, QHIGH + 1)),
                            'factor_column_grammar': 'semicolon-separated rows,p^exponent separated by *',
                            'q_prime_mask_hex': s.bithex([s.prime(q) for q in range(QLOW, QHIGH + 1)]),
                            'prime_unit_q_count': len(primes_q), 'all_prime_unit_q': primes_q,
                            'all_core_cap': 70, 'all_SF_unit_cores_gt3': core_info},
        'all_prime_q_resource_and_target_axes': q_catalog,
        'partition_complete': {'theta_demand_counts': counts, 'all_target_axis_rows': all_axes_rows,
                               'SS_resource_q_count': sum(q['SS_resources'] for q in q_catalog),
                               'S_equals_SS_plus_exact_remainder': True, 'other_cells_unpaid': True},
        'new_divided_switches': switches,
        'switch_completeness': {'all_q_SS_all_cores_linked_to_actual_switches': True,
                                'triplet_count': len(switches), 'all_six_oriented_determinants_verified': True,
                                'actual_root_polynomials_not_original17_polynomial': True,
                                'theta_exclusions_raw_not_removed': True,
                                'excluded_class_raw_proper_power_catalog': excluded_classes_raw},
        'new_selected_kernel_profiles': kernels,
        'physical_union': {'vertices': {str(m): row for m, row in sorted(physical.items())},
                           'unique_vertex_count': len(physical), 'unique_active_kernel_count': len(selected_active),
                           'literal_zero_vertex_count': len(zero_vertices),
                           'label_count': sum(len(row['labels']) for row in physical.values()),
                           'kernels_evaluated_once_by_actual_m': True, 'old_kernels_not_recomputed': True,
                           'reciprocal_m1_resources_counted_once': resources,
                           'existing_anchor_p0_count': sum(row['already_p0_anchor_vertex'] for row in resources),
                           'unique_capacity_is_existing_union_measure_not_additional_credit': True,
                           'no_capacity_credit_from_m0': True},
        'selected_measures': {
            'signed_SS_theta': h.poly_summary(signed_SS, 'sum_unique_SS_theta_demand raw(q_e)*C(e*q)'),
            'positive_debt_SS_theta': h.poly_summary(debt_SS, 'sum_unique_SS_theta_demand max(log(n_e)*C(e*q),0)'),
            'SS_raw_proper_power_signed': h.poly_summary(selected_rawpp, 'selected target proper powers,without mu(n)^2'),
            'unique_m1_capacity_measured': h.poly_summary(capacity_unique, 'sum_once_m1 max(-log(q)*C(m1),0),existing vertices'),
            'partial_SS_minus_measured_m1': h.poly_summary(partial_deficit, 'local SS positive debt minus existing unique m1 capacity'),
            'unique_physical_union_signed': h.poly_summary(physical_signed, 'sum_once_all_selected_active_physical_vertices raw_Lambda_N(n)*C(m)')},
        'selected_theta_axes_signs': selected_theta,
        'new_profile_mu_m_counts': coefficient_mu_counts,
        'properpowers_retained': {'all_target_proper_power_axes': raw_target_catalog,
                                  'resource_proper_power_axes': resource_pp,
                                  'no_mu_first_axis_squared_filter': True,
                                  'absence_if_empty_not_a_source_theorem': True},
        'local_falsifiers': falsifiers,
        'strict_logs': {'bits': s.BITS, 'scale': str(s.SCALE), 'atanh_terms': s.TERMS,
                        'method': 'same frozen exact dyadic atanh helper; signed linear/quadratic interval arithmetic'},
        'helper_bindings_sha256': {'role6/strict.py': STRICT_SHA,
                                   'role6/semiprime_helpers.py': s.digest(ROOT / 'role6' / 'semiprime_helpers.py')},
        'source_onset': 'log N >= 10^24', 'written_budget_onset': 'log N >= 10^36',
        'source_intermediate_segment_unpaid': True, 'finite_N_is_not_either_source_onset_test': True,
        'D5_D10_D11_source_bounds_not_applied': True,
        'outside_selected_SS_W_D_kernels_literal_uncomputed': True,
        'other_cells_and_raw_profiles_unpaid': True, 'T_A_and_unique_assignment_unestimated': True,
        'retained_ledger': 'D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0)',
        'strict_rational_only': True, 'Lean_called': False, 'global_D_N': False, 'victory': False}
    assert s.digest(ROOT / 'agent2_capacity_incidence.md') == REPORT_SHA
    assert s.digest(ROOT / 'previous_artifacts_sha256.json') == REGISTRY_SHA
    assert s.digest(ROOT / 'role6' / 'strict.py') == STRICT_SHA
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    output = parser.parse_args().output_dir.resolve()
    assert output == ROOT or ROOT in output.parents
    output.mkdir(parents=True, exist_ok=True)
    data = run()
    s.save(output / 'semiprime.json', data)
    print(json.dumps({'status': data['status'], 'prime_q': data['complete_window']['prime_unit_q_count'],
                      'partition': data['partition_complete'], 'physical_union_counts': {
                          key: data['physical_union'][key] for key in ['unique_vertex_count', 'unique_active_kernel_count',
                                                                    'literal_zero_vertex_count', 'existing_anchor_p0_count']},
                      'falsifiers': [{key: value for key, value in row.items() if key in ['promotion', 'status']}
                                     for row in data['local_falsifiers']], 'victory': False}), flush=True)
