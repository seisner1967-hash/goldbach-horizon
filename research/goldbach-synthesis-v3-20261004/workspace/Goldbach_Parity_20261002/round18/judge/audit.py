"""Independent Judge18: stored data, exact integer identities, fresh new Lean only.

This program is PREPARED, not authorized by its presence. run_once.py requires
the coordinator's separate authorization file. No producer is imported and no
W/D kernel, logarithm, or logarithmic sign is evaluated here.
"""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import ast
import hashlib
import json
import os
import re
import subprocess
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
SKIP = {'.lake', '.git', '.arbor', '__pycache__', '.pytest_cache', '.mypy_cache', '.ruff_cache'}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def exclusive(path, data):
    with Path(path).open('x', encoding='utf-8') as f:
        f.write(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + '\n')


def emit(stage, **data):
    print(json.dumps({'stage': stage, **data}), flush=True)


def verify_bindings(bindings, prefix):
    for name, expected in bindings.items():
        assert sha(prefix / name) == expected, ('binding_changed', name)


def input_check(inputs):
    verify_bindings(inputs['round18_sha256'], ROUND)
    verify_bindings(inputs['historical_dependencies_sha256'], BASE)
    for name, expected in inputs['original_documents_sha256'].items():
        assert sha(name) == expected, ('original_changed', name)
    assert sha(inputs['lean_executable']) == inputs['lean_sha256']
    assert sha(inputs['mathlib_HEAD_path']) == inputs['mathlib_HEAD_sha256']
    assert Path(inputs['mathlib_HEAD_path']).read_text(encoding='utf-8').strip() == inputs['mathlib_commit_expected']
    for name, expected in inputs['judge_code_sha256'].items():
        assert sha(HERE / name) == expected, ('judge_code_changed', name)


def preservation():
    registry = load(ROUND / 'previous_artifacts_sha256.json')
    assert registry['file_count'] == len(registry['sha256']) == 997
    assert registry['previous799'] == 799 and registry['round17_with_controller198'] == 198
    verify_bindings(registry['sha256'], BASE)
    actual = set()
    for folder, dirs, files in os.walk(BASE):
        dirs[:] = [d for d in dirs if d not in SKIP and
                   not (re.fullmatch(r'round\d+', d) and int(d[5:]) >= 18)]
        for name in files:
            p = Path(folder) / name
            if p != BASE / 'REPORT.md':
                actual.add(p.relative_to(BASE).as_posix())
    assert actual == set(registry['sha256']), {
        'added': sorted(actual - set(registry['sha256'])),
        'removed': sorted(set(registry['sha256']) - actual)}
    return {'files': 997, 'exact_inventory': True, 'hashes_preserved': True,
            'old_producer_kernel_sign_Lean_PDF_executed': False}


def trial_base():
    sieve = bytearray(b'\x01') * 10001
    sieve[0] = sieve[1] = 0
    for p in range(2, 101):
        if sieve[p]:
            for multiple in range(p * p, 10001, p):
                sieve[multiple] = 0
    return tuple(p for p in range(2, 10001) if sieve[p])


TRIAL_PRIMES = trial_base()


@lru_cache(maxsize=None)
def prime(n):
    assert n <= 100000000, ('primality_trial_domain_exceeded', n)
    if n < 2:
        return False
    for p in TRIAL_PRIMES:
        if p * p > n:
            return True
        if n % p == 0:
            return False
    # All primes up to sqrt(n) occur in the exhaustive base, since n <= 10^8.
    return True


def factors(n, values):
    assert 1 <= n <= 100000000
    assert prod(p ** a for p, a in values) == n
    assert len({p for p, a in values}) == len(values)
    assert list(values) == sorted(values)
    assert all(a >= 1 and prime(p) for p, a in values)
    return values


def mu(values):
    return 0 if any(a > 1 for p, a in values) else (-1) ** len(values)


def factor_columns(text):
    return [[tuple(map(int, v.split('^'))) for v in row.split('*')] if row else []
            for row in text.split(';')]


def bits(text, size):
    raw = bytes.fromhex(text)
    assert len(raw) == (size + 7) // 8
    assert not any((raw[i // 8] >> (i % 8)) & 1 for i in range(size, 8 * len(raw)))
    return [bool((raw[i // 8] >> (i % 8)) & 1) for i in range(size)]


def certs(value, path=''):
    assert not isinstance(value, float), ('float', path)
    if isinstance(value, dict):
        if {'sign', 'lower', 'upper'} <= value.keys():
            yield path, value
        for k, v in value.items():
            pointer = str(k).replace('~', '~0').replace('/', '~1')
            yield from certs(v, path + '/' + pointer)
    elif isinstance(value, list):
        for i, v in enumerate(value):
            yield from certs(v, path + '/' + str(i))


def stored_numeric_bindings():
    nm = load(ROUND / 'numeric_manifest.json')
    f6 = load(ROUND / 'role6_final_receipt.json')
    closure = load(ROUND / 'role6/closure_receipt.json')
    assert nm['files'] == len(nm['sha256']) == 67
    assert f6['bound_files'] == len(f6['sha256']) == 68
    verify_bindings(nm['sha256'], ROUND)
    verify_bindings(f6['sha256'], ROUND)
    assert sha(ROUND / 'numeric_manifest.json') == f6['numeric_manifest_sha256'] == closure['numeric_manifest_sha256']
    assert sha(ROUND / 'role6_final_receipt.json') == closure['role6_final_receipt_sha256']
    assert closure['finalizer_exit_code'] == 0
    for field, path in [('finalizer_actual_receipt_sha256', 'role6/finalize_attempt01_receipt.json'),
                        ('finalizer_log_sha256', 'role6/finalize_attempt01.log'),
                        ('finalizer_started_sha256', 'role6/finalize_attempt01_started.json'),
                        ('finalizer_snapshot_sha256', 'role6/finalize_attempt01_source.py.txt'),
                        ('finalizer_source_sha256', 'finalize_numeric.py'),
                        ('finalizer_launcher_sha256', 'role6/finalize_once.py')]:
        assert sha(ROUND / path) == closure[field]
    expected = {'typeii': {'positions': 98, 'signs': {'POSITIVE': 40, 'NEGATIVE': 25, 'ZERO': 33}},
                'semiprime': {'positions': 222, 'signs': {'POSITIVE': 151, 'NEGATIVE': 58, 'ZERO': 13}}}
    index = load(ROUND / 'role6/certificates_index.json')
    banks, counts, certificate_rows = {}, {}, {}
    for bank in ('typeii', 'semiprime'):
        p = ROUND / (bank + '.json')
        q = ROUND / ('isolated_' + bank) / (bank + '.json')
        canonical = load(ROUND / ('role6/' + bank + '_canonical_receipt.json'))
        replay = load(ROUND / ('role6/' + bank + '_replay_receipt.json'))
        assert canonical['canonical_pass'] and canonical['exit_code'] == 0
        assert replay['exit_code'] == replay['comparison_exit_code'] == 0
        assert replay['status'] == 'PASS_UNIQUE_ISOLATED_REPLAY'
        assert p.read_bytes() == q.read_bytes() and load(p) == load(q)
        assert sha(p) == sha(q) == canonical['output_sha256'] == replay['output_sha256']
        assert replay['bytes_identical'] and replay['all_fields_identical']
        data = load(p)
        assert (data['N'], data['alpha'], data['a'], data['Q'], data['M']) == (100000000, 100, 3163, 999999, 1000000)
        assert data['victory'] is False and data['global_D_N'] is False and data['Lean_called'] is False
        assert data['strict_rational_only'] is True
        rows, sign_count = [], Counter()
        for pointer, c in certs(data):
            lo, hi, sign = F(c['lower']), F(c['upper']), c['sign']
            assert lo <= hi and sign in {'POSITIVE', 'NEGATIVE', 'ZERO'}
            assert ((sign == 'POSITIVE' and lo > 0) or (sign == 'NEGATIVE' and hi < 0) or
                    (sign == 'ZERO' and lo == hi == 0)), pointer
            encoded = json.dumps(c, sort_keys=True, separators=(',', ':')).encode()
            rows.append({'json_pointer': pointer, 'sign': sign,
                         'stored_certificate_sha256': hashlib.sha256(encoded).hexdigest()})
            sign_count[sign] += 1
        assert rows == index['banks'][bank]
        counts[bank] = {'positions': len(rows), 'signs': dict(sign_count)}
        certificate_rows[bank] = rows
        banks[bank] = data
    assert counts == expected == nm['counts_by_bank']
    total = Counter()
    for c in counts.values():
        total.update(c['signs'])
    assert dict(total) == nm['sign_counts'] == {'POSITIVE': 191, 'NEGATIVE': 83, 'ZERO': 46}
    assert nm['canonical_new_bank_invocations'] == 3 and nm['unique_isolated_replays'] == 2
    assert [load(ROUND / p)['exit_code'] for p in
            ('role6/typeii_attempt01_receipt.json', 'role6/semiprime_attempt01_receipt.json',
             'role6/semiprime_attempt02_receipt.json')] == [0, 1, 0]
    return {'counts_by_bank': counts, 'combined': dict(total), 'positions': 320,
            'copies_bytes_and_fields_identical': True, 'stored_certificates': certificate_rows,
            'kernel_log_sign_recalculated': False}


def typeii_integer_audit():
    t = load(ROUND / 'typeii.json')
    pg = t['progression_complete']
    lo, hi, size, n, d = pg['b_low'], pg['b_high'], pg['integer_count'], t['N'], t['d']
    assert (lo, hi, size, d, t['V']) == (879121, 989010, 109890, 91, 10)
    bfs, jfs = factor_columns(pg['b_factorizations_complete_column']), factor_columns(pg['j_factorizations_complete_column'])
    assert len(bfs) == len(jfs) == size
    bm = bits(t['beta_structural']['mask_hex'], size)
    pm = bits(pg['theta_mask_hex'], size)
    masks = {k: bits(v['mask_hex'], size) for k, v in t['unit_conventions'].items()}
    assert set(masks) == {'0:39', '0:429', '91:39', '91:429'}
    E = t['coefficient_construction']['E']
    assert E == [17, 19]
    for row in t['coefficient_construction']['all_v_integers_tested']:
        assert row['gcd_with_K'] == gcd(row['v'], t['coefficient_construction']['K'])
    assert [r['v'] for r in t['coefficient_construction']['all_v_integers_tested']] == list(range(11, 21))
    residues = set()
    for row in t['coefficient_construction']['verified_inverses_and_residues']:
        assert row['v'] * row['inverse'] % 1001 == 1
        assert row['w_residue'] == n * row['inverse'] % 1001
        residues.add(row['w_residue'])
    assert residues == {216, 948}
    jr = Counter()
    columns, pair_count, beta_vertices, proper = {}, 0, [], []
    multiplicity = Counter()
    for i in range(size):
        b, j = lo + i, n - d * (lo + i)
        fsb, fsj = factors(b, bfs[i]), factors(j, jfs[i])
        structural = (len(fsb) == 2 and all(a == 1 for p, a in fsb) and
                      13 < fsb[0][0] and 7 * fsb[0][0] <= 3163 < 13 * fsb[0][0] < fsb[1][0] and
                      fsb[1][0] > 3163 and gcd(d * b, n) == 1)
        assert bm[i] == structural
        assert pm[i] == (fsj == [(j, 1)] and gcd(j, n) == 1)
        if structural:
            beta_vertices.append((b, fsb[0][0], fsb[1][0], d * b, j))
        if len(fsj) == 1 and fsj[0][1] > 1 and gcd(j, n) == 1:
            proper.append((b, j, fsj[0][0], fsj[0][1]))
        for k, mask in masks.items():
            assert mask[i] == (gcd(b, t['unit_conventions'][k]['gcd_modulus']) == 1)
        current = 0
        for v in range(11, 21):
            if j % v:
                continue
            w = j // v
            assert w not in columns
            columns[w] = (v, b)
            current += 1
            pair_count += 1
            in_mode = w % 1001 in residues
            assert in_mode == (v in E and b % 11 == 0)
            if in_mode:
                assert not structural
                for k, mask in masks.items():
                    jr[k] += mask[i]
        if pm[i]:
            assert current == 0
        multiplicity[str(current)] += 1
    assert len(columns) == pair_count == t['candidate_products_complete']['column_count'] == t['candidate_products_complete']['all_pair_count'] == 57189
    encoded = ''.join(f'{w},{v},{b}\n' for w, (v, b) in sorted(columns.items())).encode()
    assert hashlib.sha256(encoded).hexdigest() == t['candidate_products_complete']['columns_sorted_w_v_b_sha256']
    assert dict(multiplicity) == t['candidate_products_complete']['full_block_multiplicities']
    stored = [(v['b'], v['s'], v['q'], v['m'], v['j']) for v in t['beta_structural']['canonical_vertices']]
    assert sorted(stored) == sorted(beta_vertices) and len(stored) == len(set(stored)) == 196
    assert sum(pm) == pg['theta_candidate_count'] == 8441
    assert proper == [(v['b'], v['j'], v['factorization'][0][0], v['factorization'][0][1]) for v in t['raw_Lambda_N']['unit_proper_power_vertices']]
    assert len(proper) == t['raw_Lambda_N']['unit_proper_power_count'] == 9
    for k, mask in masks.items():
        row = t['unit_conventions'][k]
        assert sum(mask) == row['J'] and F(row['rho_exact']) == F(196, row['J'])
        assert all(not bm[i] or mask[i] for i in range(size))
    for scope, expected in [('0', 273), ('91', 234)]:
        r = t['R2_R7_R8_by_scope'][scope]
        k = scope + ':39'
        assert jr[k] == r['JR11'] == expected and jr[scope + ':429'] == 0
        assert F(r['T_adversarial_exact']) == F(t['unit_conventions'][k]['rho_exact']) * expected == F(r['L11_II_exact'])
        assert F(r['T_adversarial_normalized']) == F(20000000 * expected, t['unit_conventions'][k]['J'])
        assert F(r['corrected_T_adversarial_exact']) == 0
        assert r['finite_budget_comparison']['source_R6_not_tested']
    return {'integers': size, 'real_products': pair_count, 'beta': 196, 'theta': 8441,
            'proper_powers': 9, 'all_columns_disjoint': True, 'R2_integer_identity': True,
            'source_R6_or_global_bound_claimed': False, 'new_kernel_log_sign_executed': False}


def semiprime_integer_audit():
    s = load(ROUND / 'semiprime.json')
    n, p0, cw = s['N'], s['p0_actual_least_missing_odd_prime_finite'], s['complete_window']
    assert (cw['q_low'], cw['q_high'], cw['integer_count'], p0) == (1400100, 1405100, 5001, 3)
    fsq = factor_columns(cw['q_factorizations_complete_column'])
    assert len(fsq) == 5001
    mask = bits(cw['q_prime_mask_hex'], 5001)
    qs = []
    for i, fs in enumerate(fsq):
        q = 1400100 + i
        factors(q, fs)
        assert mask[i] == (fs == [(q, 1)])
        if mask[i] and gcd(q, n) == 1:
            qs.append(q)
    assert qs == cw['all_prime_unit_q'] and len(qs) == 333
    cores = cw['all_SF_unit_cores_gt3']
    es = [v['e'] for v in cores]
    assert len(es) == len(set(es)) == 22
    complete_es = [e for e in range(4, 71) if gcd(e, n) == 1 and
                   all(e % (p * p) != 0 for p in TRIAL_PRIMES if p * p <= e)]
    assert es == complete_es
    for v in cores:
        fs = factors(v['e'], v['factorization'])
        assert v['mu_e'] == mu(fs) and gcd(v['e'], n) == 1 and 3 < v['e'] <= 70
    counts, SSqs, axes = Counter(), [], 0
    qrows = s['all_prime_q_resource_and_target_axes']
    assert [r['q'] for r in qrows] == qs
    for r in qrows:
        q = r['q']
        for key, j in [('n1_axis', 1), ('n0_axis', 3)]:
            a = r[key]
            assert a['n'] == n - j * q
            fs = factors(a['n'], a['factorization'])
            assert a['theta_log_base'] == (a['n'] if fs == [[a['n'], 1]] else None)
            assert a['raw_Lambda_log_base'] == (fs[0][0] if len(fs) == 1 else None)
            canonical = r['n1_canonical_factor' if j == 1 else 'n0_canonical_factor']
            ell, quotient = fs[0][0], a['n'] // fs[0][0]
            assert canonical['least_prime_factor'] == ell and canonical['quotient'] == quotient
            assert canonical['quotient_prime'] == prime(quotient)
            assert canonical['canonical_small_semiprime'] == (ell <= 100 and prime(quotient))
        assert r['SS_resources'] == (r['n1_canonical_factor']['canonical_small_semiprime'] and
                                    r['n0_canonical_factor']['canonical_small_semiprime'])
        if r['SS_resources']:
            SSqs.append(q)
        assert [v['e'] for v in r['all_core_rows']] == es
        for v in r['all_core_rows']:
            axes += 1
            e, m, a = v['e'], v['m'], v['target_axis']
            assert m == e * q and a['n'] == n - m and a['n'] > s['Q']
            fs = factors(a['n'], a['factorization'])
            assert a['theta_log_base'] == (a['n'] if fs == [[a['n'], 1]] else None)
            assert a['raw_Lambda_log_base'] == (fs[0][0] if len(fs) == 1 else None)
            if v['theta_demand']:
                assert a['theta_log_base'] is not None
                counts[r['resource_partition']] += 1
                if r['resource_partition'] == 'S':
                    counts['SS' if r['SS_resources'] else 'S_minus_SS'] += 1
            if r['SS_resources']:
                sw = s['new_divided_switches'][v['switch_ref']]
                x = v['actual_x']
                assert q == sw['A'] + sw['L'] * x
                assert [aa * x + bb for aa, bb in sw['slope_constant_pairs']] == v['actual_divided_form_values']
                if not sw['target_guards']['both']:
                    assert not v['theta_demand']
            if 'kernel_ref' in v:
                assert a['raw_Lambda_log_base'] is not None and r['SS_resources']
                assert v['kernel_ref'] == str(m) and str(m) in s['new_selected_kernel_profiles']
    assert dict(counts) == s['partition_complete']['theta_demand_counts'] == {'A': 258, 'R': 32, 'S': 674, 'SS': 40, 'S_minus_SS': 634}
    assert axes == s['partition_complete']['all_target_axis_rows'] == 7326 and len(SSqs) == 14
    guarded, unguarded, saturated = 0, 0, 0
    primes = [p for p in range(2, 101) if prime(p)]
    assert len(s['new_divided_switches']) == 286
    for key, r in s['new_divided_switches'].items():
        e, l1, l0, L, A = r['e'], r['ell1'], r['ell0'], r['L'], r['A']
        assert key == f'{e}:{l1}:{l0}' and L == l1 * l0 and l1 != l0 and l0 != 3
        assert 0 <= A < L and (A - n) % l1 == (3 * A - n) % l0 == 0
        forms = [(L, A), (-e * L, n - e * A), (-l0, (n - A) // l1), (-3 * l1, (n - 3 * A) // l0)]
        assert r['slope_constant_pairs'] == [list(v) for v in forms]
        pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
        determinants = [forms[i][0] * forms[j][1] - forms[j][0] * forms[i][1] for i, j in pairs]
        assert determinants == r['oriented_determinants'] == [n * L, n * l0, n * l1, n * l0 * (1 - e), n * l1 * (3 - e), n * 2]
        delta = n ** 6 * e * 3 * L ** 6 * (e - 1) * (e - 3) * 2
        assert int(r['Delta_switch']) == abs(prod(aa for aa, bb in forms) * prod(determinants)) == delta
        guards = r['target_guards']
        both = e % l1 != 1 and e % l0 != 3 % l0
        assert guards['both'] == both
        assert guards['e_not1_mod_ell1'] == (e % l1 != 1) and guards['e_notp0_mod_ell0'] == (e % l0 != 3 % l0)
        if both:
            guarded += 1
            assert r['primitive_gcds'] == [1] * 4
        else:
            unguarded += 1
        sats = []
        for p in primes:
            rr = r['rho_actual_primes_through100'][str(p)]
            roots = [x for x in range(p) if prod(aa * x + bb for aa, bb in forms) % p == 0]
            assert roots == rr['roots'] and len(roots) == rr['rho']
            assert rr['outside_delta_switch'] == (delta % p != 0)
            if both:
                assert 1 <= len(roots) <= min(4, p)
                if p in (l1, l0):
                    assert len(roots) == 1
                if delta % p:
                    assert len(roots) == 4
            if len(roots) == p:
                sats.append(p)
        assert sats == r['saturated_primes']
        saturated += bool(sats)
        assert r['source_logarithmic_estimates_D5_D10_D11_not_applied']
        lo, hi = r['finite_x_range']
        assert r['finite_x_count'] == max(0, hi - lo + 1)
        assert r['source_x_count'] <= F(r['D2_outer_plus1_upper_exact'])
        assert r['finite_outer_plus1_kept']
        sv = r['Selberg_T3']
        if sv['status'] == 'SATURATED_EMPTY_FINITE_ROUGH_CELL':
            assert sv['rough_count'] == 0 and sv['saturated_prime'] in sats and sv['no_zero_denominator_constructed']
        else:
            assert sv['status'] == 'PASS_EXACT_NEW_DIVIDED_FORM_SELBERG_T3'
            assert F(sv['G_exact']) > 0 and F(sv['principal_exact']) == 1 / F(sv['G_exact'])
            assert F(sv['weights_exact']['1']) == 1 and all(abs(F(v)) <= 1 for v in sv['weights_exact'].values())
            assert sv['support_natural_d'] == [1, 2, 3]
            assert F(sv['square_sum_exact']) == F(r['finite_x_count']) / F(sv['G_exact']) + F(sv['paired_remainder_exact'])
            assert sv['rough_count'] <= F(sv['square_sum_exact']) <= F(sv['finite_upper_bound_exact'])
            for v in sv['CRT_classes'].values():
                assert v['actual_count'] == sum(c['count'] for c in v['class_counts_and_errors'])
                assert all(c['CRT_plus1_kept'] and abs(F(c['error_exact'])) <= 1 for c in v['class_counts_and_errors'])
    union, kernels = s['physical_union'], s['new_selected_kernel_profiles']
    assert len(union['vertices']) == union['unique_vertex_count'] == 68 and len(kernels) == union['unique_active_kernel_count'] == 54
    zeros = 0
    for key, row in union['vertices'].items():
        assert int(key) == row['m'] and row['first_axis_n'] == n - row['m']
        if 'kernel_ref' in row:
            assert row['kernel_ref'] == key and key in kernels
        else:
            zeros += 1
            assert row['literal_weighted_term'] == '0' and 'reciprocal_m0_zero_raw_axis' in row['roles']
    assert zeros == union['literal_zero_vertex_count'] == 14
    for key, k in kernels.items():
        assert k['m'] == int(key) and k['n'] == n - int(key)
        assert k['original_Q'] == s['Q'] and k['R'] == min(s['Q'], (int(key) - 1) // s['a'])
        assert k['strict_a_k_less_m'] and k['k1_joint_cancels'] and k['physical_divisor_identity_verified']
        assert not k['old_vertex_or_kernel_replayed']
        for field in ('W_kernel_exact', 'D_exact', 'C_exact'):
            assert all(isinstance(c, str) and F(c) != 0 for p, c in k[field])
    assert len(union['reciprocal_m1_resources_counted_once']) == 14 and union['existing_anchor_p0_count'] == 2
    assert s['source_intermediate_segment_unpaid'] and s['outside_selected_SS_W_D_kernels_literal_uncomputed']
    return {'q_integers': 5001, 'prime_q': 333, 'axes': axes, 'partition': dict(counts),
            'switches': 286, 'guarded': guarded, 'unguarded': unguarded, 'saturated': saturated,
            'vertices': 68, 'active_kernels_read_only': 54, 'zero_vertices': 14,
            'D5_D10_D11_or_global_payment_claimed': False, 'kernel_log_sign_recalculated': False}


def crt_annex_integer_audit():
    """Read the distinct FINAL CRT annex; no producer/helper is imported."""
    role = ROUND / 'role6_crt'
    final = load(role / 'final_receipt.json')
    manifest = load(BASE / final['manifest'])
    closure = load(role / 'closure_receipt.json')
    assert final['state'] == 'FINAL' and sha(BASE / final['manifest']) == final['manifest_sha256']
    assert sha(BASE / final['report']) == final['report_sha256']
    assert len(manifest['owned_artifacts_sha256']) == manifest['owned_bindings_count'] == 35
    assert len(manifest['read_only_inputs_sha256']) == manifest['readonly_bindings_count'] == 11
    assert len(final['bindings_sha256']) == final['bindings_count'] == 47
    assert len(closure['bindings_sha256']) == 10
    for bindings in (manifest['owned_artifacts_sha256'], manifest['read_only_inputs_sha256'],
                     final['bindings_sha256'], closure['bindings_sha256']):
        verify_bindings(bindings, BASE)
    assert final['actual_numeric_attempts'] == 1 and final['actual_numeric_failures'] == 0
    assert final['isolated_replays'] == manifest['isolated_replay_count'] == 0
    assert final['replay_authorized'] is False and final['new_log_sign_positions'] == 0
    assert closure['metadata_exit_code'] == 0 and closure['numeric_processes_rerun_by_closure'] == 0
    metadata = load(role / 'finalize_attempt01_receipt.json')
    assert metadata['actual_metadata_subprocess_returned'] and metadata['exit_code'] == 0
    assert metadata['source_sha256'] == metadata['source_after_sha256'] == metadata['source_snapshot_sha256']
    assert metadata['launcher_sha256'] == metadata['launcher_after_sha256'] == metadata['launcher_snapshot_sha256']
    assert sha(role / 'finalize_attempt01_started.json') == metadata['started_sha256']
    assert sha(role / 'finalize_attempt01.log') == metadata['log_sha256']
    canonical = load(role / 'canonical_receipt.json')
    assert canonical['exit_code'] == 0
    assert canonical['canonical_pass'] is True
    assert not (role / 'replay_receipt.json').exists()
    for receipt in (canonical,):
        assert receipt['actual_subprocess_returned'] is True
        assert receipt['post_execution_validation_error'] is None
        assert receipt['reviewed_sha256'] == receipt['source_after_sha256']
        verify_bindings(receipt['reviewed_sha256'], role)
        for name, binding in receipt['input_bindings'].items():
            assert sha(binding['path']) == binding['sha256'] == receipt['input_after_sha256'][name]
        verify_bindings(receipt['capture_sha256'], Path())
        label = receipt['kind'] + f"_attempt{receipt['attempt']:02d}"
        started = role / (label + '_started.json')
        log = role / (label + '.log')
        assert sha(started) == receipt['started_sha256'] and sha(log) == receipt['log_sha256']
        before = load(started)
        assert before['subprocess_not_started_when_capture_written'] is True
        assert before['capture_sha256'] == receipt['capture_sha256']
        assert sha(receipt['output']) == receipt['output_sha256']
    t = load(canonical['output'])
    list(certs(t))  # Recursive float rejection only; this annex adds no sign certificates.
    assert t['inputs_sha256'] == {name: b['sha256'] for name, b in canonical['input_bindings'].items()}
    assert t['contract_sha256'] == canonical['reviewed_sha256']['contract.json']
    assert t['input_registry_sha256'] == canonical['reviewed_sha256']['input_registry.json']
    assert t['producer_sha256'] == canonical['reviewed_sha256']['crt_checks.py']
    assert t['helper_sha256'] == canonical['reviewed_sha256']['crt_helpers.py']

    def rational(value):
        assert isinstance(value['numerator'], int) and isinstance(value['denominator'], int)
        assert value['denominator'] > 0
        result = F(value['numerator'], value['denominator'])
        assert result == F(value['text'])
        return result

    p = t['parameters']
    N, d, h, ell, V, A, B = (p[k] for k in ('N', 'd', 'h', 'ell', 'V', 'A', 'B'))
    assert (N, d, h, ell, V, A, B, p['x']) == (100000000, 91, 39, 11, 10, 879120, 989010, 20000000)
    H, K, length = N * d * h, N * d * h * ell, B - A
    assert (t['H'], t['K'], t['L']) == (H, K, length)
    assert gcd(ell, H) == gcd(N, d) == 1 and gcd(ell, K) == ell
    arithmetic = {}
    for label, modulus in (('H', H), ('K', K)):
        a = t[label + '_arithmetic']
        fs = [tuple(v) for v in a['factors']]
        assert fs == sorted(fs) and len({p for p, e in fs}) == len(fs)
        assert prod(p ** e for p, e in fs) == modulus and all(prime(p) and e > 0 for p, e in fs)
        density = prod(F(p - 1, p) for p, e in fs)
        assert rational(a['density']) == density > 0
        assert a['totient'] == modulus * density
        assert a['front'] == 2 ** len(fs) and a['divisor_count'] == prod(e + 1 for p, e in fs)
        arithmetic[label] = (fs, density, a['front'], a['divisor_count'])

    def divisor_fields(entries, label):
        fs, density, front, number = arithmetic[label]
        assert len(entries) == number and len({e['k'] for e in entries}) == number
        assert [e['k'] for e in entries] == sorted(e['k'] for e in entries)
        for entry in entries:
            powers = entry['exponents']
            assert len(powers) == len(fs) and all(0 <= j <= upper for j, (p, upper) in zip(powers, fs))
            assert entry['k'] == prod(p ** j for j, (p, upper) in zip(powers, fs))
            squarefree = all(j <= 1 for j in powers)
            assert entry['squarefree'] == squarefree
            assert entry['mu'] == ((-1) ** sum(powers) if squarefree else 0)
        assert sum((F(e['mu'], e['k']) for e in entries), F(0)) == density
        assert sum(abs(e['mu']) for e in entries) == front

    units = {}
    for key, label, lower, upper, modulus in (
        ('H_units', 'H', A, B, H), ('K_units', 'K', A, B, K), ('E_units', 'K', V, 2 * V, K)):
        a = t[key]
        assert (a['A_excluded'], a['B_included'], a['L'], a['modulus']) == (lower, upper, upper - lower, modulus)
        entries = a['all_divisor_counts']
        divisor_fields(entries, label)
        for e in entries:
            count = upper // e['k'] - lower // e['k']
            main = F(upper - lower, e['k'])
            assert e['direct_multiple_count'] == e['floor_multiple_count'] == count
            assert rational(e['main_term']) == main and rational(e['signed_front']) == count - main
            assert abs(count - main) <= 1 and e['front_at_most_one'] is True
        actual = [b for b in range(lower + 1, upper + 1) if gcd(b, modulus) == 1]
        included = sum(e['mu'] * e['floor_multiple_count'] for e in entries)
        assert a['direct_gcd_count'] == a['full_moebius_IE_count'] == included == len(actual)
        fs, density, front, number = arithmetic[label]
        assert rational(a['main_term']) == (upper - lower) * density
        assert rational(a['signed_front']) == len(actual) - (upper - lower) * density
        assert abs(rational(a['signed_front'])) <= a['front_bound'] == front
        assert a['front_bound_verified'] and a['every_integer_indicator_verified']
        units[key] = actual
    E = units['E_units']
    assert t['E_all_integer_unit_rows'] == E == [17, 19] and t['E_at_most_width'] == (len(E) <= V)
    deltaH, etaH = arithmetic['H'][1:3]
    deltaK, etaK = arithmetic['K'][1:3]
    pairs, checks = [], 0
    assert [row['v'] for row in t['source_H_rows']] == E
    for row in t['source_H_rows']:
        v = row['v']
        assert gcd(v, H) == gcd(v, ell) == gcd(v, d) == 1
        entries = row['all_divisor_CRT_checks']
        divisor_fields(entries, 'H')
        for e in entries:
            a, modulus = e['k'] * ell, e['k'] * ell * v
            inv_d, inv_a = e['inverse_d_mod_v'], e['inverse_kell_mod_v']
            residue_v, unique, residue = e['residue_v'], e['unique_t'], e['residue_kellv']
            assert e['v'] == v and e['modulus_kellv'] == modulus
            assert 0 <= inv_d < v and d * inv_d % v == 1
            assert 0 <= inv_a < v and a * inv_a % v == 1
            assert residue_v == N * inv_d % v and unique == residue_v * inv_a % v
            assert residue == a * unique and 0 <= residue < modulus
            assert residue % e['k'] == residue % ell == 0 and d * residue % v == N % v
            count = (B - residue) // modulus - (A - residue) // modulus
            assert e['left_direct_count'] == e['right_class_count'] == e['floor_count'] == count
            main = F(length, modulus)
            assert rational(e['main_term']) == main and rational(e['signed_front']) == count - main
            assert abs(count - main) <= 1 and e['front_at_most_one'] and e['finite_interval_equivalence']
            checks += 1
        actual = [b for b in units['H_units'] if b % ell == 0 and (N - d * b) % v == 0]
        included = sum(e['mu'] * e['floor_count'] for e in entries)
        assert row['direct_b_values'] == actual
        assert row['direct_unit_row_count'] == row['full_moebius_IE_row_count'] == included == len(actual)
        main = length * deltaH / (ell * v)
        assert rational(row['main_term']) == main and rational(row['signed_front']) == len(actual) - main
        assert abs(len(actual) - main) <= row['front_bound'] == etaH and row['row_front_bound_verified']
        pairs.extend([[v, b] for b in actual])
    assert t['omitted_pairs'] == pairs and t['JR_direct_sum_of_rows'] == len(pairs) == 234
    assert t['all_k_all_E_CRT_checks'] == checks == 1944
    assert t['J_source_H'] == len(units['H_units']) == 23185
    original = load(ROUND / 'typeii.json')
    assert t['structural_A_read_only'] == original['beta_structural']['A'] == 196
    assert t['structural_A_has_no_candidate_prime_filter'] is True
    values = {'R4a': (2 * etaK, V * deltaK), 'R4b': (etaH, length * deltaH),
              'R4c': (V * etaH, length * deltaH * deltaK / (8 * ell))}
    guards = {}
    for name, (left, right) in values.items():
        guard = t['R4_premises_only'][name]
        assert rational(guard['left']) == left and rational(guard['right']) == right
        assert guard['satisfied'] == (left <= right)
        guards[name] = guard['satisfied']
    r5 = t['R5']
    assert r5['premises_satisfied'] == all(guards.values())
    assert r5['theorem_applied'] is False and not all(guards.values())
    assert rational(r5['count_lower_left']) == values['R4c'][1]
    assert rational(r5['ratio_lower_left']) == deltaK / (16 * ell)
    assert r5['actual_JR'] == len(pairs) and rational(r5['actual_ratio']) == F(len(pairs), len(units['H_units']))
    assert r5['finite_count_comparison_only'] == (rational(r5['count_lower_left']) <= len(pairs))
    assert r5['finite_ratio_comparison_only'] == (rational(r5['ratio_lower_left']) <= rational(r5['actual_ratio']))
    corrected = t['corrected_H_times_ell']
    assert corrected['J'] == len(units['K_units']) == 21077 and corrected['JR'] == 0
    assert corrected['rows'] == [{'v': v, 'count': 0} for v in E]
    assert corrected['ell_H_coprime_guard'] is False and corrected['old_minorant_applied'] is False
    assert t['strict_integer_rational_only'] and t['logarithmic_certificates_added'] == 0
    assert t['existing_price_or_log_sign_recomputed'] is False and t['W_D_kernel_called'] is False
    assert t['Lean_called'] is False and t['source_onset_applied'] is False and t['R6_proved_or_assumed'] is False
    return {'distinct_annex': True, 'canonical_invocations': 1, 'CRT_replays': 0,
            'all_divisor_CRT_checks': checks, 'H_divisors': arithmetic['H'][3], 'K_divisors': arithmetic['K'][3],
            'E': E, 'J': len(units['H_units']), 'JR': len(pairs), 'R4_guards': guards,
            'R5_applied': False, 'corrected_JR': 0, 'old_log_sign_positions_changed': False,
            'producer_or_helper_executed': False, 'kernel_log_sign_recalculated': False}


def content_review_binding_audit():
    receipt = load(ROUND / 'role5_content/final_receipt.json')
    manifest = load(BASE / receipt['manifest'])
    assert sha(BASE / receipt['manifest']) == receipt['manifest_sha256']
    assert sha(BASE / receipt['report']) == receipt['report_sha256']
    assert len(manifest['bindings']) == manifest['bound_input_count'] == receipt['bound_inputs'] == 37
    for rel, binding in manifest['bindings'].items():
        p = BASE / rel
        assert sha(p) == binding['sha256'] and p.stat().st_size == binding['bytes']
    assert receipt['eight_sources_fully_read'] and receipt['line_numbers_verified']
    assert receipt['independent_compilation_certified_by_this_role'] is False
    assert receipt['compilation_failures_as_reported'] == 15 and receipt['failure_count_is_invocations_not_error_count']
    assert all(receipt[k] == 0 for k in ('Lean_executions', 'numeric_producer_executions',
        'kernel_executions', 'log_sign_executions', 'preflight_executions', 'PDF_executions',
        'mathematical_audit_program_executions', 'old_997_files_written'))
    return {'status': receipt['status'], 'report': receipt['report'], 'report_sha256': receipt['report_sha256'],
            'bound_inputs': 37, 'content_findings': receipt['mathematical_findings'],
            'review_is_distinct_from_fresh_compilation': True,
            'new_Global_D_N_theorem_present_in_eight_sources': False,
            'reviewer_numeric_observations_were_stored_only': True}


def author_failures(inputs):
    f3 = load(ROUND / 'role3/final_receipt.json')
    f4 = load(ROUND / 'role4/final_receipt.json')
    assert f3['state'] == 'FINAL' and f3['all_four_modules_exit0']
    assert sha(BASE / f3['manifest']) == f3['manifest_sha256']
    m3 = load(BASE / f3['manifest'])
    verify_bindings(m3['bindings'], BASE)
    verify_bindings(f4['bindings'], BASE)
    verify_bindings(f4['historical_readonly_bindings'], BASE)
    assert sha(BASE / f3['report']) == f3['report_sha256']
    assert f3['counts']['modules'] == len(f4['modules']) == 4
    assert f3['counts']['theorems'] == 60 and f4['counts_new_only']['theorems'] == 110
    records, total = [], Counter()
    for rel in inputs['author_build_ledgers']:
        data = load(ROUND / rel)
        for r in data['attempts']:
            snapshot = r.get('source_snapshot', r.get('snapshot'))
            assert snapshot and sha(snapshot) == r.get('snapshot_sha256') == r['source_sha256']
            assert sha(r['log']) == r['log_sha256']
            text = Path(r['log']).read_text(encoding='utf-8', errors='replace')
            actual_errors = [v for v in text.splitlines() if 'error:' in v]
            warnings = [v for v in text.splitlines() if 'warning:' in v]
            if r['exit_code'] != 0:
                assert actual_errors
            records.append({'ledger': rel, 'attempt': r['attempt'], 'exit_code': r['exit_code'],
                            'source': r['source'], 'snapshot': snapshot, 'source_sha256': r['source_sha256'],
                            'log': r['log'], 'log_sha256': r['log_sha256'],
                            'actual_error_lines': actual_errors, 'actual_warning_lines': warnings,
                            'Lean_generated_sorryAx_in_failed_log': r['exit_code'] != 0 and 'sorryAx' in text,
                            'analytic_parity_failure': False})
            total['invocations'] += 1
            total['failures'] += r['exit_code'] != 0
            total['warnings'] += bool(warnings)
    bookkeeping_failures = [load(p) for p in (ROUND / 'role3').glob('finalize_failed*.json')]
    return {'records': records, 'totals': dict(total),
            'author_FINAL3_manifest_and_FINAL4_bindings_verified': True,
            'bookkeeping_failure_records_retained': bookkeeping_failures,
            'failure_classification': 'TECHNICAL_API_ELABORATION_FINITESET_OR_CAST',
            'failed_declarations_validated': False, 'mathematical_parity_failure_invented': False}


def declarations(source):
    text = source.read_text(encoding='utf-8')
    stripped = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|sorryAx|trustMe)\b', stripped)
    ds = re.findall(r'^\s*(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|structure|instance)\s+([A-Za-z_][\w\u0080-\uffff\']*)', stripped, re.M)
    assert ds
    prints = re.findall(r'^\s*#print axioms\s+(\S+)', stripped, re.M)
    assert Counter(p.rsplit('.', 1)[-1] for p in prints) == Counter(n for k, n in ds)
    imports = re.findall(r'^\s*import\s+(\S+)', stripped, re.M)
    counts = Counter('theorem' if k == 'lemma' else k for k, n in ds)
    return ds, imports, counts


def compile_new(inputs):
    build = HERE / 'build'
    build.mkdir(exist_ok=True)
    results = []
    total = Counter()
    env = dict(os.environ)
    env['LEAN_PATH'] = os.pathsep.join([str(build), *inputs['historical_library_dirs'], *inputs['cache_library_dirs']])
    for rel in inputs['new_module_sources']:
        original = ROUND / rel
        module = original.stem
        receipt = HERE / (module + '_receipt.json')
        if receipt.exists():
            saved = load(receipt)
            assert saved['status'] == 'PASS_FRESH_NEW_LEAN'
            assert saved['source_sha256'] == sha(original) == sha(saved['source_snapshot'])
            assert sha(saved['olean']) == saved['olean_sha256'] and sha(saved['log']) == saved['log_sha256']
            results.append(saved)
            total.update(saved['declaration_counts'])
            continue
        source = build / original.name
        with source.open('xb') as f:
            f.write(original.read_bytes())
        snapshot = HERE / (module + '_source.lean.txt')
        with snapshot.open('xb') as f:
            f.write(source.read_bytes())
        ds, imports, counts = declarations(source)
        for imp in imports:
            if imp == 'Mathlib':
                continue
            if imp in {Path(p).stem for p in inputs['new_module_sources']}:
                assert (build / (imp + '.olean')).exists(), ('new_import_not_fresh', imp)
            else:
                assert any((Path(p) / (imp + '.olean')).is_file() for p in inputs['historical_library_dirs']), ('old_import_missing', imp)
        out, log = build / (module + '.olean'), HERE / (module + '.log')
        command = [inputs['lean_executable'], '-o', str(out), str(source)]
        started = {'status': 'PREEXEC', 'utc': datetime.now(timezone.utc).isoformat(),
                   'module': module, 'source_original': str(original), 'source_snapshot': str(snapshot),
                   'source_sha256': sha(source), 'command': command, 'cwd': str(build),
                   'LEAN_PATH': env['LEAN_PATH'], 'input_manifest_sha256': sha(HERE / 'input_manifest.json'),
                   'audit_source_sha256': sha(Path(__file__)), 'lean_sha256': sha(inputs['lean_executable']),
                   'dependency_sources_and_oleans_sha256': inputs['historical_dependencies_sha256'],
                   'fresh_imports_sha256': {r['module']: r['olean_sha256'] for r in results}}
        exclusive(HERE / (module + '_started.json'), started)
        emit('FRESH_LEAN_STARTED', module=module, declarations=len(ds))
        run = subprocess.run(command, cwd=build, env=env, capture_output=True)
        with log.open('xb') as f:
            f.write(run.stdout + run.stderr)
        text = log.read_text(encoding='utf-8', errors='replace')
        row = dict(started, finished_utc=datetime.now(timezone.utc).isoformat(),
                   exit_code=run.returncode, log=str(log), log_sha256=sha(log), olean=str(out),
                   declaration_counts=dict(counts), declarations=[n for k, n in ds], imports=imports)
        exclusive(HERE / (module + '_actual_invocation.json'), row)
        assert run.returncode == 0 and out.exists(), (module, run.returncode)
        assert not any(k in text for k in ('error:', 'sorryAx')), module
        warnings = [line for line in text.splitlines() if 'warning:' in line]
        assert all(module == 'SeparatedTypeIICount' and
                   "warning: 'push_cast' tactic does nothing" in line for line in warnings), (module, warnings)
        parsed = {}
        for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
            parsed[m.group(1)] = [p.strip() for p in m.group(2).split(',') if p.strip()]
        for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
            parsed[m.group(1)] = []
        assert len(parsed) == len(ds) and Counter(n.rsplit('.', 1)[-1] for n in parsed) == Counter(n for k, n in ds)
        assert all(set(a) <= ALLOWED for a in parsed.values())
        row.update(status='PASS_FRESH_NEW_LEAN', olean_sha256=sha(out), axioms=parsed,
                   axioms_printed=len(parsed), actual_style_warnings=warnings)
        exclusive(receipt, row)
        assert original.read_bytes() == source.read_bytes() == snapshot.read_bytes()
        results.append(row)
        total.update(counts)
        emit('FRESH_LEAN_PASS', module=module, declarations=len(parsed), olean_sha256=row['olean_sha256'])
    return {'modules': results, 'totals': {'modules': len(results), 'theorems': total['theorem'],
            'defs': total['def'], 'structures': total['structure'], 'instances': total['instance'],
            'axioms_printed': sum(r['axioms_printed'] for r in results)},
            'old_sources_or_dependencies_compiled': False, 'author18_oleans_used': False}


def stage(name, fn):
    path = HERE / (name + '_PASS.json')
    if path.exists():
        return load(path)
    emit('STAGE_STARTED', name=name)
    result = fn()
    exclusive(path, result)
    emit('STAGE_PASS', name=name, receipt_sha256=sha(path))
    return result


def main():
    inputs = load(HERE / 'input_manifest.json')
    input_check(inputs)
    before = stage('01_preservation', preservation)
    numeric = stage('02_stored_numeric', stored_numeric_bindings)
    typeii = stage('03_typeii_integers', typeii_integer_audit)
    semiprime = stage('04_semiprime_integers', semiprime_integer_audit)
    crt = stage('04b_distinct_CRT_integers', crt_annex_integer_audit)
    authors = stage('05_author_failures', lambda: author_failures(inputs))
    content = stage('05b_distinct_content_review', content_review_binding_audit)
    lean = stage('06_independent_Lean', lambda: compile_new(inputs))
    input_check(inputs)
    after = stage('07_preservation_after', preservation)
    result = {'status': 'PASS_INDEPENDENT_ROUND18_AUXILIARY_AUDIT',
              'finished_utc': datetime.now(timezone.utc).isoformat(),
              'input_manifest_sha256': sha(HERE / 'input_manifest.json'),
              'preservation_before': before, 'preservation_after': after,
              'numeric': numeric, 'typeii': typeii, 'semiprime': semiprime, 'distinct_CRT_annex': crt,
              'author_invocations': authors['totals'], 'distinct_content_review': content, 'independent_Lean': lean,
              'new_counts': lean['totals'], 'previous_counts': {'modules': 22, 'theorems': 337},
              'cumulative_counts': {'modules': 22 + lean['totals']['modules'],
                                    'theorems': 337 + lean['totals']['theorems']},
              'source_onset': 'log N >= 10^24', 'written_SS_budget_onset': 'log N >= 10^36',
              'source_R6_onset_not_formalized': True, 'D5_D10_D11_not_formalized': True,
              'source_intermediate_segment_unpaid': True, 'S_remainder634_T_A_capacity_Gamma_open': True,
              'old_numeric_or_Lean_or_PDF_executed': False, 'new_numeric_producer_called': False,
              'W_D_log_or_sign_recalculated': False,
              'score': 0, 'victory': False, 'parity_obstacle_bypass_proved': False,
              'global_D_N_target_proved': False}
    exclusive(HERE / 'audit_receipt.json', result)
    emit('AUDIT_COMPLETE_AUXILIARY_ONLY', counts=lean['totals'], score=0, victory=False)


if __name__ == '__main__':
    main()
