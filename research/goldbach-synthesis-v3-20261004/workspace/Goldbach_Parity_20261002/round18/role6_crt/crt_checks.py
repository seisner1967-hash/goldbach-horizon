"""NEW finite CRT/IE/front validation attached to Count/Lower, never a Win.

Run only through run_once.py after explicit root review.  Frozen typeii.json
is data: no previous producer, kernel, sign expression or compiler is run.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import json
from fractions import Fraction
from math import gcd
from pathlib import Path
from crt_helpers import (arithmetic_data, digest, inverse_mod, progression_values,
                         progression_floor_count, q, save_exclusive, units_check)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--contract', required=True)
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    contract_path = Path(args.contract).resolve()
    contract = json.loads(contract_path.read_text(encoding='utf-8'))
    role = contract_path.parent
    inputs_path = role / contract['input_registry']
    assert digest(inputs_path) == contract['input_registry_sha256']
    bindings = json.loads(inputs_path.read_text(encoding='utf-8'))
    for binding in bindings['inputs'].values():
        assert digest(binding['path']) == binding['sha256'], binding['path']
    data = json.loads(Path(bindings['inputs']['typeii']['path']).read_text(encoding='utf-8'))
    fixed = contract['parameters']
    N, d, h, ell, V = (fixed[name] for name in ['N', 'd', 'h', 'ell', 'V'])
    A, B, x = (fixed[name] for name in ['A', 'B', 'x'])
    H, K, L = N * d * h, N * d * h * ell, B - A
    assert [N, d, h, ell, V, A, B, x] == [100000000, 91, 39, 11, 10, 879120, 989010, 20000000]
    assert [data[name] for name in ['N', 'd', 'V', 'x', 'omitted_prime']] == [N, d, V, x, ell]
    stored_interval = data['progression_complete']
    assert stored_interval['b_low'] == A + 1 and stored_interval['b_high'] == B
    assert stored_interval['integer_count'] == L == 109890
    assert d * B <= N and 0 < V < d and gcd(N, d) == 1 and gcd(ell, H) == 1
    # Structural beta is READ as data, with no primality test of a candidate.
    beta = data['beta_structural']
    structural_A = beta['A']
    vertices = beta['canonical_vertices']
    assert structural_A == beta['canonical_unique_m_count'] == len(vertices) == 196
    assert beta['no_candidate_prime_filter'] is True
    assert int(beta['mask_hex'], 16).bit_count() == structural_A
    assert len({vertex['m'] for vertex in vertices}) == structural_A
    assert all(A < vertex['b'] <= B and vertex['m'] == d * vertex['b']
               and vertex['j'] == N - vertex['m'] and gcd(vertex['b'], H) == 1
               and vertex['b'] % ell != 0 for vertex in vertices)
    H_factors, H_divisors, deltaH, etaH, phiH = arithmetic_data(H)
    K_factors, K_divisors, deltaK, etaK, phiK = arithmetic_data(K)
    assert H_factors == [(2, 8), (3, 1), (5, 8), (7, 1), (13, 2)]
    assert K_factors == [(2, 8), (3, 1), (5, 8), (7, 1), (11, 1), (13, 2)]
    assert len(H_divisors) == 972 and len(K_divisors) == 1944
    assert (deltaH, etaH, deltaK, etaK) == (Fraction(96, 455), 32, Fraction(960, 5005), 64)
    H_units, H_units_check = units_check(A, B, H, H_divisors, deltaH, etaH)
    K_units, K_units_check = units_check(A, B, K, K_divisors, deltaK, etaK)
    E, E_check = units_check(V, 2 * V, K, K_divisors, deltaK, etaK)
    assert E == [17, 19] and len(E) <= V
    assert len(H_units) == data['unit_conventions']['91:39']['J'] == 23185
    assert len(K_units) == data['unit_conventions']['91:429']['J'] == 21077
    assert data['unit_conventions']['91:39']['gcd_modulus'] == H
    assert data['unit_conventions']['91:429']['gcd_modulus'] == K
    rows, omitted_pairs = [], []
    CRT_checks = 0
    for v in E:
        assert v > 0 and gcd(v, H) == gcd(v, ell) == gcd(d, v) == 1
        inverse_d = inverse_mod(d, v)
        residue_v = N * inverse_d % v
        assert d * residue_v % v == N % v
        # Complete direct row, separate from the CRT and Mobius construction.
        direct_row = [b for b in range(A + 1, B + 1)
                      if gcd(b, H) == 1 and b % ell == 0 and (N - d * b) % v == 0]
        row_inclusion, entries = 0, []
        for entry in H_divisors:
            k, mu = entry['k'], entry['mu']
            a, modulus = k * ell, k * ell * v
            assert gcd(k, ell) == gcd(a, v) == 1
            inverse_a = inverse_mod(a, v)
            t = residue_v * inverse_a % v
            residue = a * t
            assert 0 <= residue < modulus
            assert residue % k == residue % ell == 0
            assert d * residue % v == N % v
            # Independent finite uniqueness check, including every mu=0 divisor.
            solutions_t = [j for j in range(v) if a * j % v == residue_v]
            assert solutions_t == [t]
            # The left predicate is exhaustively enumerated by all multiples k*ell.
            first_multiple = (A // a + 1) * a
            left = [b for b in range(first_multiple, B + 1, a)
                    if (N - d * b) % v == 0]
            # The right predicate is exhaustively enumerated by the unique class.
            right = progression_values(A, B, modulus, residue)
            assert left == right, ('CRT equivalence', v, k)
            assert all(k and b % k == b % ell == 0 and (d * b - N) % v == 0
                       and (b - residue) % modulus == 0 for b in right)
            floor_count = progression_floor_count(A, B, modulus, residue)
            count = len(left)
            error = Fraction(count) - Fraction(L, modulus)
            assert count == len(right) == floor_count and abs(error) <= 1
            row_inclusion += mu * count
            CRT_checks += 1
            entries.append({**entry, 'v': v, 'inverse_d_mod_v': inverse_d,
                            'inverse_kell_mod_v': inverse_a, 'residue_v': residue_v,
                            'residue_kellv': residue, 'modulus_kellv': modulus,
                            'unique_t': t, 'left_direct_count': count,
                            'right_class_count': len(right), 'floor_count': floor_count,
                            'finite_interval_equivalence': True,
                            'main_term': q(Fraction(L, modulus)),
                            'signed_front': q(error), 'front_at_most_one': True})
        assert row_inclusion == len(direct_row)
        row_main = Fraction(L) * deltaH / (ell * v)
        row_error = Fraction(len(direct_row)) - row_main
        assert abs(row_error) <= etaH
        rows.append({'v': v, 'all_divisor_CRT_checks': entries,
                     'direct_b_values': direct_row, 'direct_unit_row_count': len(direct_row),
                     'full_moebius_IE_row_count': row_inclusion, 'main_term': q(row_main),
                     'signed_front': q(row_error), 'front_bound': etaH,
                     'row_front_bound_verified': True})
        omitted_pairs.extend([[v, b] for b in direct_row])
    JR = len(omitted_pairs)
    assert CRT_checks == len(E) * len(H_divisors) == 1944
    assert JR == sum(row['direct_unit_row_count'] for row in rows) == 234
    assert JR == data['R2_R7_R8_by_scope']['91']['JR11']
    R4 = {
        'R4a': {'left': q(2 * etaK), 'right': q(V * deltaK),
                'satisfied': 2 * etaK <= V * deltaK},
        'R4b': {'left': q(etaH), 'right': q(L * deltaH),
                'satisfied': etaH <= L * deltaH},
        'R4c': {'left': q(V * etaH), 'right': q(L * deltaH * deltaK / (8 * ell)),
                'satisfied': V * etaH <= L * deltaH * deltaK / (8 * ell)}}
    assert [R4[name]['satisfied'] for name in ['R4a', 'R4b', 'R4c']] == [False, True, False]
    premises = all(item['satisfied'] for item in R4.values())
    assert premises is False
    corrected_rows = [{'v': v, 'count': sum(gcd(b, K) == 1 and b % ell == 0
                                          and (N - d * b) % v == 0
                                          for b in range(A + 1, B + 1))} for v in E]
    corrected_JR = sum(row['count'] for row in corrected_rows)
    assert gcd(ell, K) == ell and corrected_JR == 0
    assert data['R2_R7_R8_by_scope']['91']['corrected_T_adversarial_exact'] == '0'
    result = {
        'status': 'PASS_NEW_CRT_FULL_DIVISORS_IE_AND_GUARDED_FRONTS',
        'round': 18, 'node': '13.10', 'parameters': fixed, 'H': H, 'K': K, 'L': L,
        'H_arithmetic': {'factors': H_factors, 'divisor_count': len(H_divisors),
                         'density': q(deltaH), 'totient': phiH, 'front': etaH},
        'K_arithmetic': {'factors': K_factors, 'divisor_count': len(K_divisors),
                         'density': q(deltaK), 'totient': phiK, 'front': etaK},
        'H_units': H_units_check, 'K_units': K_units_check, 'E_units': E_check,
        'E_all_integer_unit_rows': E, 'E_at_most_width': len(E) <= V,
        'source_H_rows': rows, 'all_k_all_E_CRT_checks': CRT_checks,
        'omitted_pairs': omitted_pairs, 'JR_direct_sum_of_rows': JR,
        'J_source_H': len(H_units), 'structural_A_read_only': structural_A,
        'structural_A_has_no_candidate_prime_filter': True,
        'R4_premises_only': R4,
        'R5': {'premises_satisfied': premises, 'theorem_applied': False,
               'count_lower_left': q(L * deltaH * deltaK / (8 * ell)),
               'actual_JR': JR, 'ratio_lower_left': q(deltaK / (16 * ell)),
               'actual_ratio': q(Fraction(JR, len(H_units))),
               'finite_count_comparison_only': L * deltaH * deltaK / (8 * ell) <= JR,
               'finite_ratio_comparison_only': deltaK / (16 * ell) <= Fraction(JR, len(H_units)),
               'does_not_test_source_onset_or_R6': True},
        'corrected_H_times_ell': {'J': len(K_units), 'rows': corrected_rows,
                                 'JR': corrected_JR, 'ell_H_coprime_guard': False,
                                 'old_minorant_applied': False},
        'inputs_sha256': {name: item['sha256'] for name, item in bindings['inputs'].items()},
        'contract_sha256': digest(contract_path), 'input_registry_sha256': digest(inputs_path),
        'producer_sha256': digest(Path(__file__)),
        'helper_sha256': digest(Path(__file__).with_name('crt_helpers.py')),
        'strict_integer_rational_only': True, 'logarithmic_certificates_added': 0,
        'previous_320_sign_positions_untouched': True,
        'old_producers_or_banks_rerun': False, 'W_D_kernel_called': False,
        'existing_price_or_log_sign_recomputed': False, 'Lean_called': False,
        'source_onset_applied': False, 'R6_proved_or_assumed': False,
        'Gamma_global_controlled': False, 'global_D_N_controlled': False,
        'score': 0, 'victory': False}
    output_dir = Path(args.output_dir).resolve()
    assert output_dir.is_dir()
    output = output_dir / 'crt.json'
    save_exclusive(output, result)
    print(json.dumps({'status': result['status'], 'all_CRT_checks': CRT_checks,
                      'J': len(H_units), 'JR': JR, 'J_corrected': len(K_units),
                      'JR_corrected': corrected_JR,
                      'R4': {name: value['satisfied'] for name, value in R4.items()},
                      'theorem_R5_applied': False, 'victory': False}, sort_keys=True))


if __name__ == '__main__':
    main()
