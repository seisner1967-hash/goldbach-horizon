"""Selected new d91 separated-row TypeII contract, all six checks of FINAL1 §8."""
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

ROOT = Path(__file__).resolve().parent
REPORT_SHA = '228766a630e37e4cee7f92bc46cb862582da59379b15653f4c00abcbc37313f0'
REGISTRY_SHA = '05212665afffecade91134e1533f93d11eba8058179198e4420eef1fe252f2bc'
C, R, D, X, V, ELL = 7, 13, 91, 20000000, 10, 11
BLO, BHI = 879121, 989010
HVALUES, SCOPES = (39, 429), (0, 91)


def key(scope, h):
    return str(scope) + ':' + str(h)


def summary_scalar(value, expression):
    return {'exact_rational': str(value), 'expression': expression,
            'sign_certificate': s.scalar_certificate(value)}


def summary_vector(value, expression):
    return {'exact_expression': expression, 'nonzero_formal_prime_terms': len(value),
            'sign_certificate': s.vector_certificate(value)}


def run():
    assert s.digest(ROOT / 'agent1_calibrated_typeii.md') == REPORT_SHA
    assert s.digest(ROOT / 'previous_artifacts_sha256.json') == REGISTRY_SHA
    assert (s.ALPHA - 1) ** 4 < s.N <= s.ALPHA ** 4
    assert (s.A - 1) ** 16 < s.N ** 7 <= s.A ** 16
    assert (s.M - 1) ** 4 < s.N ** 3 <= s.M ** 4 and s.Q == (s.N - 1) // s.ALPHA
    assert C * R == D and X == s.N // 5 and (V - 1) ** 8 < s.N <= V ** 8
    assert gcd(D, s.N) == 1 and V < D and ELL * ELL < s.A
    assert BLO == s.ceildiv(s.N - X, D) and BHI == s.ceildiv(s.N - X // 2, D) - 1
    size = BHI - BLO + 1
    jlow, jhigh = s.N - D * BHI, s.N - D * BLO
    assert (size, jlow, jhigh) == (109890, 10000090, 19999989)
    assert s.Q < jlow and jhigh < 4473 ** 2

    # Coefficients are fixed here, before ANY candidate primality or theta read.
    H = s.rad_components(s.N, D, 39)
    K = s.rad_components(s.N, D, 39, ELL)
    allv = list(range(V + 1, 2 * V + 1))
    tested_v = [{'v': v, 'factorization': s.factor(v), 'gcd_with_K': gcd(v, K)} for v in allv]
    E = [row['v'] for row in tested_v if row['gcd_with_K'] == 1]
    assert E == [17, 19] and K == H * ELL and K == s.rad_components(s.N, D, 429)
    modulus = D * ELL
    inverses = [{'v': v, 'inverse': pow(v, -1, modulus),
                 'w_residue': s.N * pow(v, -1, modulus) % modulus} for v in E]
    for row in inverses:
        assert row['v'] * row['inverse'] % modulus == 1
    residues = {row['w_residue'] for row in inverses}
    assert len(residues) == len(E) and modulus == 1001

    own_primes = [p for p in s.PRIMES if p <= 4472]
    q_primes = [p for p in own_primes if p <= 3940]
    svalues = [p for p in own_primes if 244 <= p <= 451 and p > R and C * p <= s.A < R * p]
    assert min(svalues) == 251 and max(svalues) <= 451 and BHI // min(svalues) == 3940
    beta, vertices, fibres = bytearray(size), [], []
    unique_m = set()
    for p in svalues:
        lower = max(s.A, R * p, s.ceildiv(BLO, p) - 1)
        upper = BHI // p
        all_q = [q for q in q_primes if lower < q <= upper]
        kept, removed = [], []
        for q in all_q:
            if gcd(C * R * p * q, s.N) != 1:
                removed.append(q)
                continue
            b, m = p * q, D * p * q
            j = s.N - m
            assert BLO <= b <= BHI and not beta[b - BLO]
            assert p > R and C * p <= s.A < R * p < q and q > s.A
            assert len({C, R, p, q}) == 4 and C * R * p > s.A
            assert s.M <= m <= s.N - 2 and X // 2 < j <= X and j > s.Q
            assert gcd(b, D * 429 * s.N) == 1 and b % ELL != 0
            assert m not in unique_m
            unique_m.add(m)
            beta[b - BLO] = 1
            kept.append(q)
            vertices.append({'b': b, 's': p, 'q': q, 'm': m, 'j': j,
                             'factorization_b': s.factor(b), 'canonical_once': True})
        fibres.append({'s': p, 'q_strict_lower': lower, 'q_inclusive_upper': upper,
                       'all_q_primes': all_q, 'q_unit_retained': kept, 'q_unit_removed': removed})
    A = sum(beta)
    assert A == len(vertices) == len(unique_m)
    masks, Js, densities = {}, {}, {}
    for scope in SCOPES:
        for h in HVALUES:
            k = key(scope, h)
            actual_modulus = (D if scope else 1) * h * s.N
            mask = bytearray(gcd(b, actual_modulus) == 1 for b in range(BLO, BHI + 1))
            J = sum(mask)
            assert all(not beta[i] or mask[i] for i in range(size))
            assert J > 0 or A == 0
            masks[k], Js[k] = mask, J
            densities[k] = Fraction(A, J) if J else Fraction(0)
        assert all(masks[key(scope, 429)][i] == bool(masks[key(scope, 39)][i] and (BLO + i) % ELL)
                   for i in range(size))
    print(json.dumps({'stage': 'complete_structural_beta_and_fixed_coefficients', 'A': A,
                      'J': Js, 'E_from_all_integers': E, 'kappa_residues_mod1001': sorted(residues)}), flush=True)

    # Enumerate real products over ALL rows 11..20; separation concerns columns w.
    ns = [s.N - D * b for b in range(BLO, BHI + 1)]
    pairs, product_rows, column_owner = [], [], {}
    multiplicity_full = [0] * size
    multiplicity_E = [0] * size
    eta = [0] * size
    JR = {k: 0 for k in masks}
    R1beta, R1U = 0, {k: 0 for k in masks}
    for v in allv:
        if gcd(v, D) != 1:
            assert all(j % v != 0 for j in ns)
            product_rows.append({'v': v, 'count': 0, 'reason': 'v_not_unit_d_and_N_unit_d'})
            continue
        residue_b = s.N * pow(D, -1, v) % v
        first, last = BLO + (residue_b - BLO) % v, BHI - (BHI - residue_b) % v
        count = 0 if first > last else (last - first) // v + 1
        wlo, whi = (X // 2) // v + 1, X // v
        for b in range(first, last + 1, v):
            i, j = b - BLO, s.N - D * b
            assert j % v == 0 and X // 2 < j <= X
            w = j // v
            assert wlo <= w <= whi and v * w == j
            assert gcd(v, D) == gcd(w, D) == 1
            assert w not in column_owner, ('column_separation_failed', w, column_owner.get(w), (v, b))
            column_owner[w] = (v, b)
            kappa = -1 if w % modulus in residues else 0
            expected = -1 if v in E and b % ELL == 0 else 0
            assert kappa == expected, ('periodic_coefficient_identity_false', v, b, w, kappa, expected)
            coefficient = kappa if v in E else 0
            pairs.append((v, b, w, coefficient))
            multiplicity_full[i] += 1
            if v in E:
                multiplicity_E[i] += 1
                eta[i] += coefficient
            R1beta += beta[i]
            for k, mask in masks.items():
                R1U[k] += mask[i]
                if coefficient:
                    assert not beta[i]
                    JR[k] += mask[i]
        product_rows.append({'v': v, 'xi_adversarial': int(v in E), 'b_residue_mod_v': residue_b,
                             'b_first': first, 'b_last': last, 'b_step': v, 'count': count,
                             'w_window_low': wlo, 'w_window_high': whi,
                             'w_at_first': (s.N - D * first) // v, 'w_at_last': (s.N - D * last) // v,
                             'w_step': -D, 'complete_recipe': 'b=first+t*v,0<=t<count;j=N-91b;w=j/v'})
    assert len(pairs) == len(column_owner) == sum(multiplicity_full)
    assert sum(row['count'] for row in product_rows) == len(pairs)
    assert all(eta[i] == (-multiplicity_E[i] if (BLO + i) % ELL == 0 else 0) for i in range(size))
    assert all(not beta[i] or eta[i] == 0 for i in range(size))
    R1 = {}
    for k, mask in masks.items():
        rho, direct, witness = densities[k], Fraction(0), Fraction(0)
        codes = bytearray((len(pairs) + 3) // 4)
        counts = {-1: 0, 0: 0, 1: 0}
        for index, (v, b, w, coefficient) in enumerate(pairs):
            z = Fraction(beta[b - BLO]) - rho * mask[b - BLO]
            sign = 1 if z > 0 else (-1 if z < 0 else 0)
            counts[sign] += 1
            codes[index // 4] |= {0: 0, 1: 1, -1: 2}[sign] << (2 * (index % 4))
            direct += abs(z)
            witness += sign * z
        expected = R1beta * (1 - rho) + (R1U[k] - R1beta) * rho
        assert direct == witness == expected
        R1[k] = {'all_v_block': allv, 'all_columns_distinct': True,
                 'xi_all_ones': True, 'kappa_sign_by_column_packed_2bits_hex': codes.hex(),
                 'coefficient_code_grammar': 'pairs ordered v then b;2bits each:0=zero,1=+1,2=-1',
                 'coefficient_counts': {str(a): n for a, n in counts.items()},
                 'beta_pair_count': R1beta, 'unit_pair_count': R1U[k],
                 'operator_l1': summary_scalar(direct, 'sum_pairs abs(beta(b)-rho*U(b))'),
                 'complete_sign_witness_verified': True, 'arbitrary_coefficient_upper_bound_triangle': True}

    # Full theta/raw axes are now inspected; they did not determine kappa.
    prime_mask, allpp, rawpp = bytearray(size), [], []
    theta_beta, raw_beta, IIraw_beta = {}, {}, {}
    theta_U, raw_U, IIraw_U = ({k: {} for k in masks} for _ in range(3))
    II_beta, II_U = 0, {k: 0 for k in masks}
    forbidden_class = s.N * pow(D, -1, ELL) % ELL
    classrows = [{'b_residue_mod11': t, 'all_b': 0, 'beta': 0, 'theta': 0,
                  'unit_counts': {k: 0 for k in masks}, 'raw_proper_power_b': []} for t in range(ELL)]
    for i, j in enumerate(ns):
        b, nf, unit = BLO + i, s.factor(j), gcd(j, s.N) == 1
        isprime = nf == ((j, 1),)
        theta = {j: Fraction(1)} if isprime and unit else {}
        raw = {nf[0][0]: Fraction(1)} if len(nf) == 1 and unit else {}
        if theta:
            prime_mask[i] = 1
            assert j > 2 * V and multiplicity_full[i] == 0 and eta[i] == 0
            assert b % ELL != forbidden_class
        row = classrows[b % ELL]
        row['all_b'] += 1
        row['beta'] += beta[i]
        row['theta'] += bool(theta)
        if len(nf) == 1 and nf[0][1] > 1:
            record = {'b': b, 'j': j, 'factorization': nf, 'unit_N': unit,
                      'raw_log_prime': nf[0][0] if unit else None, 'adversarial_eta': eta[i],
                      'multiplicity_full': multiplicity_full[i], 'multiplicity_E': multiplicity_E[i]}
            allpp.append(record)
            if unit:
                rawpp.append(record)
                row['raw_proper_power_b'].append(b)
        if beta[i]:
            s.add(theta_beta, theta)
            s.add(raw_beta, raw)
            s.add(IIraw_beta, raw, eta[i])
            II_beta += eta[i]
        for k, mask in masks.items():
            if mask[i]:
                row['unit_counts'][k] += 1
                s.add(theta_U[k], theta)
                s.add(raw_U[k], raw)
                s.add(IIraw_U[k], raw, eta[i])
                II_U[k] += eta[i]
    assert II_beta == 0 and all(II_U[k] == -JR[k] for k in masks)
    assert classrows[forbidden_class]['theta'] == 0 and forbidden_class != 0
    assert sum(prime_mask) == sum(row['theta'] for row in classrows)
    for k in masks:
        assert sum(row['unit_counts'][k] for row in classrows) == Js[k]
    neighbors = []
    for p in E:
        exponent, power = 1, p
        while power * p <= jlow:
            exponent += 1
            power *= p
        following = power * p
        assert power < jlow <= jhigh < following
        neighbors.append({'prime': p, 'below_power': power, 'below_exponent': exponent,
                          'above_power': following, 'above_exponent': exponent + 1,
                          'no_prime_power_of_this_base_in_candidate_window': True})
    assert all(not vector for vector in IIraw_U.values()) and not IIraw_beta
    print(json.dumps({'stage': 'complete_products_and_axes', 'pairs_all_v': len(pairs),
                      'theta_candidates': sum(prime_mask), 'raw_unit_proper_powers': len(rawpp),
                      'JR11': JR}), flush=True)

    functionals, prices, R2, falsifiers = {}, {}, {}, []
    normalization = Fraction(X, A) if A else None
    weights = {'theta': (theta_beta, theta_U), 'II': (II_beta, II_U),
               'II_raw': (IIraw_beta, IIraw_U), 'raw': (raw_beta, raw_U)}
    all_z = {}
    for weight, (primitive_beta, primitive_U) in weights.items():
        scalar = weight == 'II'
        def scale(value, coefficient):
            return value * coefficient if scalar else s.scaled(value, coefficient)
        def minus(left, right):
            return left - right if scalar else s.difference(left, right)
        def plus(left, right):
            if scalar:
                return left + right
            out = dict(left)
            s.add(out, right)
            return out
        def summarize(value, expression):
            return summary_scalar(value, expression) if scalar else summary_vector(value, expression)
        refs = {k: scale(primitive_U[k], densities[k]) for k in masks}
        z = {k: minus(primitive_beta, refs[k]) for k in masks}
        all_z[weight] = z
        rows = {}
        for k in masks:
            rows[k] = {'reference': summarize(refs[k], {'primitive_mask': k, 'weight': weight, 'scale': str(densities[k])}),
                       'z_functional': summarize(z[k], {'beta_weight': weight, 'reference': k, 'reference_scale': str(-densities[k])})}
            if normalization is not None:
                rows[k]['normalized_x_over_A'] = summarize(scale(z[k], normalization),
                                                            {'z_mask': k, 'weight': weight, 'scale': str(normalization)})
        E91 = {h: minus(refs[key(91, h)], refs[key(0, h)]) for h in HVALUES}
        L11 = {scope: minus(refs[key(scope, 429)], refs[key(scope, 39)]) for scope in SCOPES}
        for h in HVALUES:
            assert z[key(0, h)] == plus(z[key(91, h)], E91[h])
        for scope in SCOPES:
            assert z[key(scope, 39)] == plus(z[key(scope, 429)], L11[scope])
        assert minus(L11[91], L11[0]) == minus(E91[429], E91[39])
        assert z[key(0, 39)] == plus(plus(z[key(91, 429)], L11[91]), E91[39])
        functionals[weight] = {'beta_primitive': summarize(primitive_beta, {'primitive': 'beta', 'weight': weight}),
                              'unit_primitives': {k: summarize(v, {'primitive_mask': k, 'weight': weight}) for k, v in primitive_U.items()},
                              'by_mask': rows}
        prices[weight] = {'E91': {str(h): summarize(v, {'reference_plus': key(91, h), 'reference_minus': key(0, h), 'weight': weight}) for h, v in E91.items()},
                          'L11': {str(scope): summarize(v, {'reference_plus': key(scope, 429), 'reference_minus': key(scope, 39), 'weight': weight}) for scope, v in L11.items()},
                          'full_calibration_square_and_telescope_exact': True, 'weight': weight}
        if scalar:
            for scope in SCOPES:
                k, corrected = key(scope, 39), key(scope, 429)
                expected = densities[k] * JR[k]
                assert z[k] == expected and z[corrected] == 0 and L11[scope] == expected
                assert JR[corrected] == 0
                record = {'JR11': JR[k], 'T_adversarial_exact': str(expected),
                          'corrected_T_adversarial_exact': str(z[corrected]),
                          'L11_II_exact': str(L11[scope]), 'R2_R7_R8_verified': True}
                if normalization is not None:
                    normalized = expected * normalization
                    ratio = Fraction(JR[k], Js[k])
                    assert normalized == X * ratio
                    record['T_adversarial_normalized'] = str(normalized)
                    record['T_normalized_over_x'] = str(ratio)
                    lo, hi = s.log_bounds(X)
                    budget_lo, budget_hi = Fraction(X) / hi ** 2, Fraction(X) / lo ** 2
                    lower, upper = normalized - budget_hi, normalized - budget_lo
                    certificate = s.certify_bounds(lower, upper)
                    record['finite_budget_comparison'] = {
                        'proposed_finite_promotion': '|TII_hat|<=x/log(x)^2 for all coefficients',
                        'sign_certificate': certificate, 'budget_lower': str(budget_lo), 'budget_upper': str(budget_hi),
                        'status': 'LOCAL_PROMOTION_FALSIFIED' if certificate['sign'] == 'POSITIVE' else 'NO_COUNTEREXAMPLE',
                        'source_R6_not_tested': True, 'no_global_impossibility': True}
                    if certificate['sign'] == 'POSITIVE':
                        falsifiers.append({'scope': scope, 'guard': 'A>0 and J>0',
                                           'status': 'LOCAL_PROMOTION_FALSIFIED',
                                           'witness': 'fixed periodic kappa1001, xi=1_E; same beta without j-prime filter',
                                           'sign_certificate': certificate, 'no_global_impossibility': True})
                R2[str(scope)] = record
    # Exact R9 and R10 keep raw proper powers apart from theta.
    calibration_details = {}
    for scope in SCOPES:
        k, kp = key(scope, 39), key(scope, 429)
        T0 = s.difference(theta_U[k], theta_U[kp])
        R0 = s.difference(raw_U[k], raw_U[kp])
        explicit_theta = s.scaled(theta_U[k], densities[kp] - densities[k])
        s.add(explicit_theta, T0, -densities[kp])
        explicit_raw = s.scaled(raw_U[k], densities[kp] - densities[k])
        s.add(explicit_raw, R0, -densities[kp])
        Ltheta = s.difference(s.scaled(theta_U[kp], densities[kp]), s.scaled(theta_U[k], densities[k]))
        Lraw = s.difference(s.scaled(raw_U[kp], densities[kp]), s.scaled(raw_U[k], densities[k]))
        assert explicit_theta == Ltheta and explicit_raw == Lraw
        pp_price = s.difference(Lraw, Ltheta)
        explicit_pp = {}
        for row in rawpp:
            i = row['b'] - BLO
            coefficient = densities[kp] * masks[kp][i] - densities[k] * masks[k][i]
            s.add(explicit_pp, {row['raw_log_prime']: Fraction(1)}, coefficient)
        assert explicit_pp == pp_price
        calibration_details[str(scope)] = {
            'theta_removed_class_primitive': summary_vector(T0, {'theta_mask': k, 'b_mod11': 0}),
            'raw_removed_class_primitive': summary_vector(R0, {'raw_mask': k, 'b_mod11': 0}),
            'R9_exact': True, 'R10_exact': True,
            'raw_minus_theta_price': summary_vector(pp_price, {'sum': 'proper powers only', 'coefficient': 'rho429*U429-rho39*U39'}),
            'theta_price_different_functional_from_II_and_IIraw': True}
    logs = sorted(set(ns[i] for i in range(size) if prime_mask[i]) |
                  {row['raw_log_prime'] for row in rawpp} | {X, 2})
    log_catalog = {str(p): [str(v) for v in s.log_dyadic(p)] for p in logs}
    multiplicities = lambda seq: {str(a): seq.count(a) for a in sorted(set(seq))}
    columns_hash = s.sha256(''.join(f'{w},{v},{b}\n' for w, (v, b) in sorted(column_owner.items())).encode()).hexdigest()
    result = {
        'status': 'PASS_NEW_D91_SEPARATED_ROW_IDENTITY_AND_LOCAL_PROMOTION_TEST' if A else 'EMPTY_STRUCTURAL_FIBRE',
        'round': 18, 'contract_FINAL1_sha256': REPORT_SHA, 'protected_registry_sha256': REGISTRY_SHA,
        'N': s.N, 'c': C, 'r': R, 'd': D, 'x': X, 'V': V, 'omitted_prime': ELL,
        'alpha': s.ALPHA, 'a': s.A, 'Q': s.Q, 'M': s.M,
        'progression_complete': {'b_low': BLO, 'b_high': BHI, 'integer_count': size,
                                 'j_low': jlow, 'j_high': jhigh, 'candidate_integer_span': jhigh - jlow + 1,
                                 'row_recipe': 'b=879121+i,j=N-91b,0<=i<109890',
                                 'b_factorizations_complete_column': s.factor_column(range(BLO, BHI + 1)),
                                 'j_factorizations_complete_column': s.factor_column(ns),
                                 'factor_column_grammar': 'semicolon-separated rows,p^exponent separated by *',
                                 'theta_mask_hex': s.bithex(prime_mask), 'theta_candidate_count': sum(prime_mask),
                                 'bit_order': 'low bit i%8 in byte i//8'},
        'own_completeness': {'s_first': min(svalues), 's_cap': 451, 'q_cap': 3940,
                             's_all_primes': svalues, 'q_own_prime_base': q_primes,
                             'candidate_factor_trial_limit': 4472, 'candidate_own_prime_base': own_primes,
                             'all_candidates_and_proper_powers_examined': True},
        'beta_structural': {'A': A, 'mask_hex': s.bithex(beta), 'canonical_vertices': vertices,
                            'canonical_unique_m_count': len(unique_m), 'physical_fibres': fibres,
                            'no_candidate_prime_filter': True, 'no_W_or_D_kernel_computed': True},
        'unit_conventions': {k: {'scope': int(k.split(':')[0]), 'h': int(k.split(':')[1]),
                                  'J': Js[k], 'rho_exact': str(densities[k]), 'mask_hex': s.bithex(masks[k]),
                                  'gcd_modulus': (D if k.startswith('91:') else 1) * int(k.split(':')[1]) * s.N,
                                  'J_zero_implies_A_zero': True} for k in masks},
        'coefficient_construction': {'H': H, 'K': K, 'all_v_integers_tested': tested_v, 'E': E,
                                     'modulus': modulus, 'verified_inverses_and_residues': inverses,
                                     'kappa_recipe': '-1 iff w mod1001 is a listed residue,else0',
                                     'xi_recipe': '1 iff v in E,else0', 'norms_at_most_one': True,
                                     'constructed_before_theta_or_candidate_primality': True},
        'candidate_products_complete': {'all_v_rows': product_rows, 'all_pair_count': len(pairs),
                                        'column_count': len(column_owner), 'all_columns_distinct': True,
                                        'columns_sorted_w_v_b_sha256': columns_hash,
                                        'full_block_multiplicities': multiplicities(multiplicity_full),
                                        'E_multiplicities': multiplicities(multiplicity_E),
                                        'analytic_multiplicity_retained_no_physical_resource_created': True,
                                        'all_prime_candidates_product_multiplicity_zero': True},
        'R1_complete_column_sign_certificate': R1, 'R2_R7_R8_by_scope': R2,
        'functionals_exact': functionals, 'prices_by_weight': prices,
        'R9_R10_details': calibration_details, 'normalization_x_over_A': str(normalization) if normalization is not None else None,
        'class_counts_mod11': classrows, 'candidate11_forbidden_class': forbidden_class,
        'forbidden_class_theta_zero_guard_j_greater_Q_greater11': True,
        'raw_Lambda_N': {'all_proper_power_factorizations': allpp, 'unit_proper_power_vertices': rawpp,
                         'unit_proper_power_count': len(rawpp), 'E_prime_power_neighbors': neighbors,
                         'II_adversarial_raw_zero_verified_but_other_proper_powers_retained': True,
                         'no_mu_candidate_squared_filter': True},
        'strict_logs': {'bits': s.BITS, 'scale': str(s.SCALE), 'atanh_terms': s.TERMS,
                        'method': 'outward-rounded positive atanh series,exact rational geometric tail,base2 reduction',
                        'dyadic_numerator_bounds_catalog': log_catalog},
        'local_promotion_falsifiers': falsifiers,
        'source_onset': 'log N >= 10^24', 'source_onset_applied_to_finite_N': False,
        'source_R3_R4_R5_R6_not_claimed_by_finite_test': True,
        'D_W_errors_literal_uncomputed': 'all physical W/D,other fibres and source ledger terms remain uncomputed and unpaid',
        'Gamma_aggregate_unestimated': True, 'whole_TypeII_not_upper_bounded': True,
        'strict_rational_only': True, 'Lean_called': False, 'global_D_N': False, 'victory': False,
        'helper_sha256': s.digest(ROOT / 'role6' / 'strict.py')}
    assert s.digest(ROOT / 'agent1_calibrated_typeii.md') == REPORT_SHA
    assert s.digest(ROOT / 'previous_artifacts_sha256.json') == REGISTRY_SHA
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    assert output == ROOT or ROOT in output.parents
    output.mkdir(parents=True, exist_ok=True)
    data = run()
    s.save(output / 'typeii.json', data)
    print(json.dumps({'status': data['status'], 'A': data['beta_structural']['A'],
                      'J': {k: v['J'] for k, v in data['unit_conventions'].items()},
                      'theta': data['progression_complete']['theta_candidate_count'],
                      'proper_powers': data['raw_Lambda_N']['unit_proper_power_count'],
                      'R2': data['R2_R7_R8_by_scope'], 'victory': False}), flush=True)
