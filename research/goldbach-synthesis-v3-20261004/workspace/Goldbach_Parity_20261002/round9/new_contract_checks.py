"""New round9 contracts only: raised face and actual weighted operator.

N=10^8 is a finite arithmetic probe, never an analytic onset certificate.
Receipts are isolated under round9; all historical production files are frozen.
"""
import sys
sys.dont_write_bytecode = True
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from fractions import Fraction
from math import gcd, prod
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parent
spec = spec_from_file_location('round9_shared_contracts', ROOT / 'shared.py')
shared = module_from_spec(spec)
spec.loader.exec_module(shared)
N, factor, divisors, mu = shared.N, shared.factor, shared.divisors, shared.mu
add, multiply = shared.vector_add, shared.multiply_vectors
log_vector, serialize = shared.log_vector, shared.serialize
ALPHA, Q, H, A9 = 100, 999999, 1000, 3163


def phi(k):
    return prod(p ** (e - 1) * (p - 1) for p, e in factor(k))


def Lambda(n, unit=True):
    if not 1 < n < N or (unit and gcd(n, N) != 1):
        return {}
    fs = factor(n)
    return {(fs[0][0],): Fraction(1)} if len(fs) == 1 else {}


def logr(m, k):
    value = log_vector(m)
    add(value, log_vector(k), -1)
    return value


def kernels(m, face, min_k=1):
    n = N - m
    D, W = {}, {}
    prefix = min(Q, (m - 1) // face)
    for k in divisors(m):
        if min_k <= k <= Q and face * k < m:
            add(D, logr(m, k), -mu(k))
    for k in range(min_k, prefix + 1):
        if gcd(k, n * N) == 1:
            add(W, logr(m, k), Fraction(-mu(k), phi(k)))
    return D, W


def S_lambda(m, face):
    coefficient = Lambda(N - m)
    if not coefficient or mu(m) == 0:
        return {}
    D, W = kernels(m, face)
    K = dict(D)
    add(K, W, -1)
    return {key: mu(m) * value for key, value in multiply(coefficient, K).items()}


def P_band(m, version, min_k=1):
    coefficient = Lambda(N - m, unit=(version == 'V2_Lambda_N'))
    result = {}
    for k in divisors(m):
        r = m // k
        if not (min_k <= k <= Q and ALPHA < r <= A9):
            continue
        if version in ('V1_literal', 'V2_unit_mask'):
            if gcd(r, k * N) != 1:
                continue
            if version == 'V2_unit_mask' and gcd(k, N) != 1:
                continue
        elif gcd(k, r) != 1:
            continue
        add(result, multiply(coefficient, log_vector(r)), mu(k) ** 2 * mu(r))
    return result


def Z_face(m, min_k=1):
    coefficient = Lambda(N - m)
    if not coefficient or mu(m) == 0:
        return {}
    _, W0 = kernels(m, ALPHA, min_k)
    _, W9 = kernels(m, A9, min_k)
    difference = dict(W0)
    add(difference, W9, -1)
    return {key: mu(m) * value for key, value in multiply(coefficient, difference).items()}


def line_k3(m):
    assert 3 * A9 < m <= N - 2
    coefficient = Lambda(N - m)
    value = multiply(coefficient, logr(m, 3))
    residue_formula = {}
    if m % 3 == 2:
        add(residue_formula, value, Fraction(mu(m), 2))
    if m % 3 == 0:
        add(residue_formula, value, Fraction(-mu(m), 2))
    physical = Fraction(int(m % 3 == 0))
    model = Fraction(int(gcd(3, (N - m) * N) == 1), 2)
    direct = {key: mu(m) * mu(3) * (physical - model) * c
              for key, c in value.items() if mu(m) * (physical - model) * c}
    assert direct == residue_formula
    return direct


def face_checks():
    assert (A9 - 1) ** 16 < N ** 7 <= A9 ** 16
    assert H ** 8 <= N ** 3 < (H + 1) ** 8
    assert Q == (N - 1) // ALPHA
    samples = (173, 303, 311, 323, 2121, 3183, 9507, 32421,
               112211, 658911, 1017399, N - 2)
    rows = []
    for m in samples:
        left = S_lambda(m, ALPHA)
        add(left, S_lambda(m, A9), -1)
        p2 = P_band(m, 'V2_Lambda_N')
        assert p2 == P_band(m, 'V2_unit_mask')
        z = Z_face(m)
        right = {}
        add(right, p2, -1)
        add(right, z, -1)
        assert left == right, (m, left, right)
        p_ge2 = P_band(m, 'V2_Lambda_N', 2)
        z_ge2 = Z_face(m, 2)
        right_ge2 = {}
        add(right_ge2, p_ge2, -1)
        add(right_ge2, z_ge2, -1)
        assert left == right_ge2, (m, left, right_ge2)
        rows.append(dict(m=m, n=N-m, mu=mu(m), m_factors=factor(m),
                         n_factors=factor(N-m), difference=serialize(left),
                         P_band_V2_all_k=serialize(p2), Z_face_all_k=serialize(z),
                         P_band_V2_ge2=serialize(p_ge2), Z_face_ge2=serialize(z_ge2)))
    head_left, head_right, k1_balance = {}, {}, {}
    for m in range(1, 1025):
        add(head_left, S_lambda(m, ALPHA))
        add(head_left, S_lambda(m, A9), -1)
        add(head_right, P_band(m, 'V2_Lambda_N'), -1)
        add(head_right, Z_face(m), -1)
        add(k1_balance, P_band(m, 'V2_Lambda_N'))
        add(k1_balance, P_band(m, 'V2_Lambda_N', 2), -1)
        add(k1_balance, Z_face(m))
        add(k1_balance, Z_face(m, 2), -1)
    assert head_left == head_right and not k1_balance
    bad_m = N - 2
    original = P_band(bad_m, 'V1_literal')
    assert original == multiply(log_vector(2), log_vector(161))
    assert not P_band(bad_m, 'V2_Lambda_N')
    assert gcd(161, 621118*N) == 1 and gcd(621118, N) == 2
    assert 161 * 621118 == bad_m and 621118 <= Q
    assert not S_lambda(bad_m, ALPHA) and not Z_face(bad_m)
    harmful, favorable = line_k3(32421), line_k3(9507)
    expected_harm = {}
    add(expected_harm, multiply(log_vector(99967579), log_vector(10807)), Fraction(1,2))
    expected_fav = {}
    add(expected_fav, multiply(log_vector(99990493), log_vector(3169)), Fraction(-1,2))
    assert harmful == expected_harm and favorable == expected_fav
    assert shared.polynomial_sign_certificate(harmful)['sign'] == 'POSITIVE'
    assert shared.polynomial_sign_certificate(favorable)['sign'] == 'NEGATIVE'
    assert not Lambda(N-31209)
    power_row = next(row for row in rows if row['m'] == 1017399)
    assert power_row['difference'] and not power_row['P_band_V2_all_k']
    assert not power_row['P_band_V2_ge2'] and power_row['Z_face_ge2']
    assert Lambda(N-1017399) == log_vector(9949) and mu(N-1017399)**2 == 0
    assert not P_band(2121, 'V2_Lambda_N')
    assert P_band(2121, 'V2_Lambda_N', 2) == multiply(Lambda(N-2121),log_vector(2121))
    return dict(status='PASS_IDENTITY_ONLY_CORRECTED_V2',
                samples=rows, head_domain='m=1..1024; no tail enumeration',
                head_difference=serialize(head_left), k1_balance=serialize(k1_balance),
                rejected_V1=dict(status='ERROR_FALSIFIER',m=bad_m,r=161,k=621118,n=2,
                                 extra=serialize(original),reason='Missing k-unit mask with ordinary Lambda'),
                line_k3_harmful=serialize(harmful), line_k3_favorable=serialize(favorable),
                rejected_candidate_m31209=dict(n_factors=factor(N-31209),Lambda_N_zero=True))


def weighted_operator_checks():
    samples = (303,311,323,658911,112211)
    J = (3,7,11,13)
    gram = {(k,l):{} for k in J for l in J}
    energy, DD, DM, MD, MM, B, B_weighted = {}, {}, {}, {}, {}, {}, {}
    rows = []
    for m in samples:
        n = N-m
        lam = Lambda(n)
        weight = {key:mu(m)**2*c for key,c in lam.items() if mu(m)**2*c}
        avec, dvec, hvec = {}, {}, {}
        for k in J:
            assert gcd(k,N) == 1
            t = int(m%k == 0 and H*k < m)
            h = Fraction(int(ALPHA*k < m and gcd(k,n*N)==1),phi(k))
            dvec[k] = {key:t*c for key,c in logr(m,k).items() if t*c}
            hvec[k] = {key:h*c for key,c in logr(m,k).items() if h*c}
            avec[k] = dict(dvec[k])
            add(avec[k],hvec[k],-1)
        A, D, M = {}, {}, {}
        for k in J:
            add(A,avec[k],mu(k)); add(D,dvec[k],mu(k)); add(M,hvec[k],mu(k))
        add(energy,multiply(weight,multiply(A,A)))
        add(DD,multiply(weight,multiply(D,D)))
        add(DM,multiply(weight,multiply(D,M)))
        add(MD,multiply(weight,multiply(M,D)))
        add(MM,multiply(weight,multiply(M,M)))
        add(B,multiply(lam,A),mu(m))
        add(B_weighted,multiply(weight,A),mu(m))
        for k in J:
            for l in J:
                add(gram[k,l],multiply(weight,multiply(avec[k],avec[l])))
        rows.append(dict(m=m,n=n,mu_m=mu(m),mu_n_squared=mu(n)**2,
                         n_factors=factor(n),Lambda_N=serialize(lam),
                         weight=serialize(weight),a={str(k):serialize(avec[k]) for k in J}))
    contraction = {}
    for k in J:
        for l in J:
            add(contraction,gram[k,l],mu(k)*mu(l))
    assert contraction == energy
    assert B == B_weighted
    expansion = dict(DD)
    add(expansion,DM,-1); add(expansion,MD,-1); add(expansion,MM)
    assert expansion == energy
    assert not Lambda(N-311)
    assert Lambda(N-658911) == log_vector(9967) and mu(N-658911)**2 == 0
    assert mu(112211) == 0 and Lambda(N-112211)
    model = next(row for row in rows if row['m']==323)
    assert model['a']['3'] and not (323%3==0 and H*3<323)
    assert mu(323)==1 and factor(N-323)==((99999677,1),)
    diagonal = multiply(Lambda(N-323),multiply(logr(323,3),logr(323,3)))
    diagonal = {key:c/4 for key,c in diagonal.items()}
    assert shared.polynomial_sign_certificate(diagonal)['sign']=='POSITIVE'
    q, k, m = 3, 3, 658911
    assert k % q == 0 and m % k == 0 and H*k < m
    assert gcd(N,q)==1 and (N-m)%q == N%q == 1
    raw311, raw311_metadata = shared.actual_profile(311)
    assert raw311 and not Lambda(N-311)
    return dict(status='PASS_IDENTITY_ONLY_WEIGHTED_ENERGY',
                domain=dict(m=list(samples),J=list(J),alpha=ALPHA,H=H),rows=rows,
                B_J=serialize(B),energy=serialize(energy),
                gram={f'{k},{l}':serialize(v) for (k,l),v in gram.items()},
                DD=serialize(DD),DM=serialize(DM),MD=serialize(MD),MM=serialize(MM),
                genuine_model_only_diagonal_m323=serialize(diagonal),
                rejected_prime_claim_m311=dict(status='ERROR_FALSIFIER',
                    n_factors=factor(N-311),Lambda_N_zero=True,raw=serialize(raw311)),
                native_phase_q_divides_k=dict(q=q,k=k,m=m,r=m//k,
                    n_residue=(N-m)%q,N_residue=N%q,quadratic_character_ratio=1),
                properpower_analytic_payment_tested=False,
                analytic_gain=False,rank_one_assumed=False)


if __name__ == '__main__':
    destination = shared.output_directory()
    before = shared.verify()
    result = dict(status='FINITE_NEW_CONTRACT_CHECKS_ONLY',N=N,
                  face=face_checks(),weighted_operator=weighted_operator_checks(),
                  analytic_onset=dict(source_u_min='10^24',BV_threshold='unevaluated'),
                  victory=False,Lean_called=False,imports=shared.IMPORTS,
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  conservation_before=before,conservation_after=shared.verify())
    output = destination / 'new_contracts.json'
    output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,
                         face_status=result['face']['status'],
                         weighted_status=result['weighted_operator']['status'],
                         conservation=result['conservation_after'],output=str(output)),indent=2))
