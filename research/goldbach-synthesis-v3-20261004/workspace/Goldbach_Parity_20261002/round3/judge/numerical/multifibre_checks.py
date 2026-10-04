"""Exact finite multi-fibre checks at N=100000000; no global D_N claim.

Logs use rational artanh bounds after reduction to [1,2]. No floating-point
arithmetic decides a sign. Existing numerical sources and receipts are read-only.
"""
import sys
sys.dont_write_bytecode = True
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import gcd
from pathlib import Path
from time import perf_counter
import json

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
sys.path.insert(0, str(BASE/'numerical'))
from parity_checks import N, PRIMES, direct_HU, factor, mu, rough
from round2_checks import local_term

ALPHA = 100
Q = (N-1)//ALPHA
M_CAP = 20000


def serialize_fraction(q):
    return f'{q.numerator}/{q.denominator}'


def serialize_quadratic(vector):
    return {f'{p},{r}': serialize_fraction(c) for (p,r),c in sorted(vector.items()) if c}


def vector_add(target, source, scale=1):
    for key, c in source.items():
        target[key] = target.get(key, Fraction(0))+scale*c
        if target[key] == 0:
            del target[key]


@lru_cache(None)
def artanh_log_bounds(x, terms):
    assert 1 <= x <= 2 and terms >= 1
    z = (x-1)/(x+1)
    z2 = z*z
    power, lower = z, Fraction(0)
    for j in range(terms):
        lower += 2*power/Fraction(2*j+1)
        power *= z2
    tail_upper = 2*power/(Fraction(2*terms+1)*(1-z2))
    assert tail_upper >= 0
    return lower, lower+tail_upper


@lru_cache(None)
def log_prime_bounds(p, terms):
    assert p > 1
    exponent = p.bit_length()-1
    scaled = Fraction(p, 2**exponent)
    assert 1 <= scaled < 2
    log2_lower, log2_upper = artanh_log_bounds(Fraction(2), terms)
    log_scaled_lower, log_scaled_upper = artanh_log_bounds(scaled, terms)
    lower = exponent*log2_lower+log_scaled_lower
    upper = exponent*log2_upper+log_scaled_upper
    assert 0 < lower <= upper
    # Outward rounding to a common rational denominator preserves the
    # proof enclosure and avoids multiplying thousands of unrelated large
    # denominators when summing a whole finite scalar. This is integer
    # division, not floating-point rounding.
    denominator = 10**(2*terms)
    lower_num = (lower.numerator*denominator)//lower.denominator
    upper_num = -((-upper.numerator*denominator)//upper.denominator)
    rounded_lower,rounded_upper = Fraction(lower_num,denominator),Fraction(upper_num,denominator)
    assert 0 < rounded_lower <= lower <= upper <= rounded_upper
    return rounded_lower,rounded_upper


def sign_certificate(vector):
    if not vector:
        return dict(sign='ZERO', justification='All exact symbolic coefficients vanish',
                    terms=0, lower='0/1', upper='0/1')
    for terms in (6, 12, 24, 48):
        lower = upper = Fraction(0)
        for (p,r), c in vector.items():
            lp, up = log_prime_bounds(p, terms)
            lr, ur = log_prime_bounds(r, terms)
            if c > 0:
                lower += c*lp*lr
                upper += c*up*ur
            else:
                lower += c*up*ur
                upper += c*lp*lr
        assert lower <= upper
        if upper < 0 or lower > 0:
            return dict(sign='NEGATIVE' if upper < 0 else 'POSITIVE',
                        justification='Rational artanh bounds enclose every log and every signed product',
                        terms=terms, lower=serialize_fraction(lower), upper=serialize_fraction(upper))
    return dict(sign='UNRESOLVED', terms=terms,
                lower=serialize_fraction(lower), upper=serialize_fraction(upper))


@lru_cache(None)
def actual_term(m):
    n = N-m
    assert 1 < n < N and 1 <= m < N and gcd(n,N) == 1
    metadata, coefficients = local_term(m)
    return metadata, coefficients


def selected_term(m):
    """Original unit kernel with explicit extra first-axis squarefree selector."""
    if gcd(m,N) != 1 or mu(m) == 0 or mu(N-m) == 0:
        return {}
    return actual_term(m)[1]


def pair_scan(counts):
    signs = Counter()
    first = {}
    rejected = Counter()
    p_domain = (3,7,11,13,17,19)
    for p in p_domain:
        assert p <= ALPHA and gcd(p,N) == 1 and factor(p) == ((p,1),)
        for m in range(1, M_CAP//p+1):
            pm = p*m
            if m % p == 0:
                rejected['p_divides_m'] += 1
                continue
            if gcd(m,N) != 1:
                rejected['nonunit_complement'] += 1
                continue
            if mu(m) == 0 or mu(pm) == 0:
                rejected['nonsquarefree_complement_axis'] += 1
                continue
            if mu(N-m) == 0 or mu(N-pm) == 0:
                rejected['nonsquarefree_first_axis'] += 1
                continue
            assert rough(N-m,2) and rough(N-pm,2)
            assert mu(pm) == -mu(m)
            original, cv = actual_term(m)
            switched, dv = actual_term(pm)
            paired = dict(cv)
            vector_add(paired,dv)
            # Transport identity at the actual moving endpoints, not a
            # surrogate with frozen n, prefix, harmonic mask, or modulus.
            transported = {key: Fraction(mu(m))*c for key,c in cv.items()}
            vector_add(transported, {key: Fraction(mu(pm))*c for key,c in dv.items()}, -1)
            transported = {key: Fraction(mu(m))*c for key,c in transported.items()}
            assert paired == transported
            cert = sign_certificate(paired)
            signs[cert['sign']] += 1
            counts['actual_two_site_transport_identity'] += 1
            counts['actual_pair_sign_certificate'] += 1
            key = cert['sign']
            if key not in first:
                first[key] = dict(p=p,m=m,pm=pm,
                                  original_alpha_rough=rough(m,ALPHA),
                                  switched_alpha_rough=rough(pm,ALPHA),
                                  original=original,switched=switched,
                                  pair_coefficients=serialize_quadratic(paired),certificate=cert)
    assert signs['NEGATIVE'] > 0
    return dict(p_domain=p_domain,m_cap=M_CAP,
                domain='Every 1<=m<=floor(20000/p), p-free, unit to N, both m and pm squarefree, both N-m and N-pm squarefree',
                first_axis_roughness='W=2; retained exactly on all accepted pairs',
                rough_alpha_selector='Recorded on each example, not imposed; departing faces are retained',
                accepted=sum(signs.values()),signs=dict(signs),rejected=dict(rejected),
                first_example_by_sign=first)


def four_site_check(counts):
    p,q,base = 3,7,101
    block = {}
    sites = []
    for d in (1,p,q,p*q):
        m = d*base
        assert gcd(m,N) == 1 and mu(m) and mu(N-m)
        assert rough(N-m,2)
        metadata, cv = actual_term(m)
        vector_add(block,cv)
        sites.append(metadata)
    assert sites[2]['literal_kernel'] == {'3':'1/2','7':'-1/2','101':'1/3'}
    assert factor(N-p*q*base) == ((99997879,1),)
    assert sites[0]['fII'] != {} and sites[0]['literal_kernel'] == {}
    assert sites[3]['fII'] == {}
    cert = sign_certificate(block)
    assert cert['sign'] == 'NEGATIVE'
    counts['actual_four_site_block_with_moving_prefixes'] += 1
    return dict(p=p,q=q,base=base,sites=sites,
                block_coefficients=serialize_quadratic(block),certificate=cert,
                verdict='Strictly negative actual Sfull block; pointwise favorable closure is false')


def finite_global_transport(counts):
    cap = 1000
    direct = {}
    for m in range(1,cap+1):
        vector_add(direct,selected_term(m))
    receipts = []
    for p in (3,7):
        paired, tails = {}, {}
        bases = paired_bases = tail_bases = 0
        for base in range(1,cap+1):
            if base % p == 0 or mu(base) == 0 or gcd(base,N) != 1:
                continue
            bases += 1
            if p*base <= cap:
                pair = dict(selected_term(base))
                vector_add(pair,selected_term(p*base))
                vector_add(paired,pair)
                paired_bases += 1
            else:
                vector_add(tails,selected_term(base))
                tail_bases += 1
        recombined = dict(paired)
        vector_add(recombined,tails)
        assert recombined == direct
        counts['finite_global_transport_with_unpaired_upper_face'] += 1
        receipts.append(dict(p=p,cap=cap,bases=bases,paired_bases=paired_bases,
                             upper_face_bases=tail_bases,
                             identity='Direct scalar sum equals paired base sum plus retained unpaired upper face',
                             upper_face_symbolic_nonzero=bool(tails)))
    return dict(cap=cap,first_axis_extra_selector='mu(N-m)^2',receipts=receipts,
                direct_sign=sign_certificate(direct),
                scope='Finite cap only; every omitted partner above cap is kept in the upper face')


def histogram_convolution(left,right,N_modulus):
    out = Counter()
    for x,c in left.items():
        for y,d in right.items():
            out[x*y % N_modulus] += c*d
    return Counter({x:c for x,c in out.items() if c})


def spectral_histogram_check(counts):
    a_values = tuple(a for a in range(1,121) if gcd(a,N) == 1 and mu(a))
    st_values = tuple(s for s in range(1,61) if gcd(s,N) == 1 and mu(s))
    A = {a:direct_HU(a,2)[0] for a in a_values}
    S = {s:mu(s) for s in st_values}
    T = {t:mu(t) for t in st_values}
    inv = {s:pow(s,-1,N) for s in st_values}
    assert all(s*inverse % N == 1 for s,inverse in inv.items())
    direct,coupled = Counter(),Counter()
    triples = 0
    for a in a_values:
        for s in st_values:
            for t in st_values:
                eta = -a*pow(s*t,-1,N) % N
                coefficient = A[a]*S[s]*T[t]
                direct[eta] += coefficient
                if a < s:
                    coupled[eta] += coefficient
                triples += 1
    direct = Counter({eta:c for eta,c in direct.items() if c})
    coupled = Counter({eta:c for eta,c in coupled.items() if c})
    A_push = Counter({-a % N:c for a,c in A.items() if c})
    S_inv = Counter({inv[s]:c for s,c in S.items()})
    T_inv = Counter({inv[t]:c for t,c in T.items()})
    factorized = histogram_convolution(histogram_convolution(A_push,S_inv,N),T_inv,N)
    assert direct == factorized and direct != coupled
    difference = sorted(set(direct)|set(coupled))
    first_eta = next(eta for eta in difference if direct[eta] != coupled[eta])
    counts['separable_exact_unit_quotient_histogram'] += 1
    counts['coupled_selector_factorization_counterexample'] += 1
    return dict(N=N,y=2,a_interval=[1,120],s_t_interval=[1,60],
                selector='Separate squarefree and unit masks on a,s,t; product-squarefree or moving faces are not assumed separable',
                triples=triples,nonzero_quotient_residues=len(direct),
                status='PASS: direct quotient histogram equals three-factor group convolution',
                direct_histogram_sha256=sha256(json.dumps(sorted(direct.items()),separators=(',',':')).encode()).hexdigest(),
                false_coupled_factorization=dict(selector='a<s',eta=first_eta,
                                                factorized_coefficient=direct[first_eta],
                                                actual_coupled_coefficient=coupled[first_eta]))


def gauss_phase_check(q,counts):
    assert factor(q) == ((q,1),)
    chi = {x:1 if pow(x,(q-1)//2,q) == 1 else -1 for x in range(1,q)}
    assert sum(chi.values()) == 0
    phases,gauss_squared = [0]*q,[0]*q
    for eta in range(1,q):
        for x in range(1,q):
            phases[(eta*x+pow(x,-1,q)) % q] += chi[eta]
            gauss_squared[(eta+x) % q] += chi[eta]*chi[x]
    assert phases == gauss_squared
    expected_sign = chi[q-1]
    assert phases[0] == expected_sign*(q-1)
    assert all(c == -expected_sign for c in phases[1:])
    exact_value = phases[0]-phases[1]
    assert exact_value == expected_sign*q and exact_value != 0
    counts['exact_Legendre_Kloosterman_Gauss_phase_histogram'] += 1
    return dict(q=q,character='Legendre',phase_at_zero=phases[0],phase_at_nonzero=phases[1],
                exact_value_after_sum_of_nontrivial_qth_roots_equals_minus_one=exact_value,
                scope='Exact finite phase coefficients; no conductor-uniform saving inferred')


def primitive_point_mass_check(counts):
    modulus, conductor = 1658,829
    a,s,t,b,k = 15,7,11,13,19
    n,m = a*b,s*t*k
    assert n+m == modulus and mu(n) and mu(m) and gcd(n,modulus) == 1
    assert rough(n,2) and gcd(a,modulus) == gcd(s*t,modulus) == 1
    eta = -a*pow(s*t,-1,modulus) % modulus
    character = 1 if pow(eta % conductor,(conductor-1)//2,conductor) == 1 else -1
    coefficient = direct_HU(a,2)[0]*direct_HU(s*t,2)[0]
    assert coefficient == 4 and coefficient*character != 0
    counts['unit_squarefree_HH_point_mass_nonzero_primitive_character'] += 1
    return dict(N=modulus,conductor=conductor,a=a,s=s,t=t,b=b,k=k,n=n,m=m,
                eta=eta,HH_coefficient=coefficient,Legendre_character=character,
                projected_point_mass=coefficient*character,
                scope='Separate finite diagnostic; not the N=1e8 analytical sector or cutoff onset')


def snapshot_previous():
    return {str(path.relative_to(BASE)):sha256(path.read_bytes()).hexdigest()
            for path in (BASE/'numerical').rglob('*')
            if path.is_file() and '__pycache__' not in path.parts}


def run():
    start = perf_counter()
    before = snapshot_previous()
    counts = Counter()
    four_sites = four_site_check(counts)
    pairs = pair_scan(counts)
    transport = finite_global_transport(counts)
    spectrum = spectral_histogram_check(counts)
    gauss = [gauss_phase_check(q,counts) for q in (11,829)]
    point_mass = primitive_point_mass_check(counts)
    after = snapshot_previous()
    assert before == after
    result = dict(status='PASS',N=N,alpha=ALPHA,Q=Q,
                  sign_oracle='Certified rational artanh-series bounds with exact range reduction; no floating log oracle',
                  checks=dict(counts),four_site_counterexample=four_sites,
                  actual_pair_scan=pairs,finite_global_transport=transport,
                  separable_spectral_histogram=spectrum,gauss_phase_diagnostics=gauss,
                  primitive_HH_point_mass=point_mass,
                  previous_numerical_artifacts_preserved=True,
                  previous_artifact_sha256=before,
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  limitations='No global D_N bound; accepted finite domains and their boundary faces are explicit',
                  elapsed_seconds=round(perf_counter()-start,3))
    (ROOT/'multifibre.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k] for k in ('status','N','alpha','Q','checks',
                                          'gauss_phase_diagnostics','previous_numerical_artifacts_preserved',
                                          'script_sha256','elapsed_seconds')},indent=2))
    print(json.dumps(dict(pair_sign_counts=pairs['signs'],accepted_pairs=pairs['accepted'],
                         four_site_sign=four_sites['certificate']['sign'],
                         spectral_residues=spectrum['nonzero_quotient_residues'],
                         coupled_selector_counterexample=spectrum['false_coupled_factorization']),indent=2))


if __name__ == '__main__':
    run()
