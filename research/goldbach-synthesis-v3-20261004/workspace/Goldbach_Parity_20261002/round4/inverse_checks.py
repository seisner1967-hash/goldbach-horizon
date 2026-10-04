"""Exact inverse-completion, nonunit remainders, and coupled C=s*t tests.

Cyclic exponential sums are integer phase histograms reduced modulo the exact
cyclotomic polynomial. No complex or floating-point approximation is used.
"""
import sys
sys.dont_write_bytecode = True
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import gcd, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
sys.path.insert(0,str(BASE/'numerical'))
from parity_checks import N, factor


def trim(poly):
    out = list(poly)
    while out and out[-1] == 0:
        out.pop()
    return out


def polynomial_division(poly,monic):
    remainder = trim(poly)
    divisor = trim(monic)
    assert divisor and divisor[-1] == 1
    quotient = [0]*max(0,len(remainder)-len(divisor)+1)
    while len(remainder) >= len(divisor):
        degree = len(remainder)-len(divisor)
        coefficient = remainder[-1]
        quotient[degree] = coefficient
        for i,value in enumerate(divisor):
            remainder[degree+i] -= coefficient*value
        remainder = trim(remainder)
    return trim(quotient),remainder


@lru_cache(None)
def cyclotomic(q):
    poly = [-1]+[0]*(q-1)+[1]
    for d in range(1,q):
        if q % d == 0:
            poly,remainder = polynomial_division(poly,cyclotomic(d))
            assert not remainder
    assert poly[-1] == 1
    return tuple(poly)


def reduce_phases(phases,q):
    return tuple(polynomial_division(phases,cyclotomic(q))[1])


def cyclic_convolution(left,right,q):
    out = [0]*q
    for i,c in enumerate(left):
        if c:
            for j,d in enumerate(right):
                if d:
                    out[(i+j)%q] += c*d
    return out


def add(target,source,scale=1):
    for i,c in enumerate(source):
        target[i] += scale*c


def character(q,conductor):
    assert factor(conductor) == ((conductor,1),)
    assert q % conductor == 0
    return tuple(0 if gcd(x,q) != 1 else
                 (1 if pow(x % conductor,(conductor-1)//2,conductor) == 1 else -1)
                 for x in range(q))


def Fhat(F,h,q):
    phases = [0]*q
    for z,c in F.items():
        phases[-h*z % q] += c
    return phases


def g_character(chi,h,q):
    phases = [0]*q
    for x,c in enumerate(chi):
        phases[h*x % q] += c
    return phases


def inverse_axis(F,q,chi):
    H,E = [0]*q,[0]*q
    for h in range(q):
        hat = Fhat(F,h,q)
        if gcd(h,q) == 1:
            add(H,hat,chi[h])
        else:
            add(E,cyclic_convolution(hat,g_character(chi,h,q),q))
    tau = g_character(chi,1,q)
    tauH = cyclic_convolution(tau,H,q)
    Fchi = sum(c*chi[z % q] for z,c in F.items())
    target = [-c for c in E]
    target[0] += q*Fchi
    assert reduce_phases(tauH,q) == reduce_phases(target,q)
    return dict(H=H,E=E,tau=tau,tauH=tauH,Fchi=Fchi,target=target)


def constant_value(reduced):
    assert len(reduced) <= 1
    return reduced[0] if reduced else 0


def inverse_test(q,conductor):
    chi = character(q,conductor)
    assert sum(chi) == 0
    F,G = {1:1},{1:1}
    first,second = inverse_axis(F,q,chi),inverse_axis(G,q,chi)
    tau_squared = constant_value(reduce_phases(cyclic_convolution(first['tau'],first['tau'],q),q))
    tauH = constant_value(reduce_phases(first['tauH'],q))
    E = constant_value(reduce_phases(first['E'],q))
    assert tauH == q-E
    double_lhs = cyclic_convolution(first['tauH'],second['tauH'],q)
    double_rhs = cyclic_convolution(first['target'],second['target'],q)
    assert reduce_phases(double_lhs,q) == reduce_phases(double_rhs,q)
    unit_projection = Fraction(constant_value(reduce_phases(double_lhs,q)),q*q)
    assert unit_projection == Fraction(tauH*tauH,q*q)
    if q == 11:
        assert (tau_squared,tauH,E,unit_projection) == (-11,11,0,Fraction(1))
    if q == 15:
        assert (tau_squared,tauH,E,unit_projection) == (-3,3,12,Fraction(1,25))
    if q == 100:
        assert (tau_squared,tauH,E,unit_projection) == (0,0,100,Fraction(0))
    # A second finite pair of full supports also tests the exact remainder
    # identity, without restricting F and G to point masses.
    F_general = {z:z%7-3 for z in range(q) if gcd(z,q) == 1}
    G_general = {z:(3*z+1)%11-5 for z in range(q) if gcd(z,q) == 1}
    general_f,general_g = inverse_axis(F_general,q,chi),inverse_axis(G_general,q,chi)
    assert reduce_phases(cyclic_convolution(general_f['tauH'],general_g['tauH'],q),q) == \
        reduce_phases(cyclic_convolution(general_f['target'],general_g['target'],q),q)
    return dict(q=q,conductor=conductor,tau_squared=tau_squared,tau_H_delta1=tauH,
                nonunit_remainder_delta1=E,
                exact_double_unit_projection=f'{unit_projection.numerator}/{unit_projection.denominator}',
                primal_delta1_projection=1,
                dropping_remainder_is_false=unit_projection != 1,
                cyclotomic=cyclotomic(q),
                general_support_Fchi=general_f['Fchi'],general_support_Gchi=general_g['Fchi'],
                all_h_retained='Unit h in H and every nonunit h in E')


def large_N_orbit_test():
    assert factor(N) == ((2,8),(5,8))
    step = N//5
    assert step % 10 == 0 and step*5 == N
    phi_N = prod(p**(e-1)*(p-1) for p,e in factor(N))
    assert phi_N == 40000000 and phi_N//5 == 8000000
    classes = []
    for x in (1,3,7,9):
        orbit = tuple((x+j*step) % N for j in range(5))
        assert len(set(orbit)) == 5
        assert all(gcd(y,N) == 1 and y % 5 == x % 5 for y in orbit)
        chi = 1 if pow(x % 5,2,5) == 1 else -1
        classes.append(dict(unit_class_mod10=x,chi_mod5=chi,orbit=orbit))
    assert reduce_phases([1]*5,5) == ()
    return dict(N=N,conductor=5,step=step,unit_count=phi_N,orbit_count=phi_N//5,
                all_unit_classes_mod10=classes,
                phase_identity='Each orbit contributes chi(x)*e_N(x)*(1+zeta5+zeta5^2+zeta5^3+zeta5^4)=0',
                tau_exact=0,
                consequence_for_F_delta1='The exact completion identity requires E=N; dropping all nonunit h loses the whole primal mass',
                scope='Exact five-residue-class orbit argument covers the unit group; no enumeration of 40000000 units and no asymptotic estimate')


def dual_phase_histogram(F,G,q,eta,b,units_h_l_only=False):
    h_values = tuple(h for h in range(q) if not units_h_l_only or gcd(h,q) == 1)
    units = tuple(x for x in range(q) if gcd(x,q) == 1)
    inverses = {x:pow(x,-1,q) for x in units}
    phases = [0]*q
    for z,c in F.items():
        for k,d in G.items():
            for x in units:
                A = (eta*b*x-z) % q
                B = (inverses[x]-k) % q
                for h in h_values:
                    for l in h_values:
                        phases[(h*A+l*B) % q] += c*d
    return phases


def energy_product_histogram(F,G,q):
    integer,cyclic = Counter(),Counter()
    terms = []
    for z,c in F.items():
        for k,d in G.items():
            assert 1 <= z*k < q
            integer[z*k] += c*d
            cyclic[z*k % q] += c*d
            terms.append((z*k,c*d))
    assert integer == cyclic
    energy = sum(c*c for c in cyclic.values())
    collisions = sum(c*d for m,c in terms for n,d in terms if m % q == n % q)
    assert energy == collisions
    return dict(product_histogram=dict(sorted(cyclic.items())),energy=energy,
                exact_weighted_collision_count=collisions,
                scope='All products are strictly below q; cyclic collisions are literal integer collisions')


def coupled_C_test():
    q,R,K,a,b = 100,70,3,1,1
    G = {k:1 for k in range(1,K+1) if gcd(k,q) == 1}
    receipts = []
    supports = {}
    for s,t in ((3,7),(3,11)):
        C = s*t
        assert gcd(C,q) == 1
        F = {z:1 for z in range(1,R//C+1) if gcd(z,q) == 1}
        supports[C] = F
        eta = -a*pow(C,-1,q) % q
        P = sum(c*d for z,c in F.items() for k,d in G.items() if z*k % q == eta*b % q)
        phases = dual_phase_histogram(F,G,q,eta,b)
        reduced = reduce_phases(phases,q)
        assert reduced == (() if P == 0 else (q*q*P,))
        unit_only = reduce_phases(dual_phase_histogram(F,G,q,eta,b,True),q)
        receipts.append(dict(s=s,t=t,C=C,Z=R//C,eta=eta,F_support=list(F),G_support=list(G),
                             primal=P,full_dual_numerator=constant_value(reduced),denominator=q*q,
                             unit_h_l_only_reduced=unit_only,
                             energy=energy_product_histogram(F,G,q),
                             phases_sha256=sha256(json.dumps(phases,separators=(',',':')).encode()).hexdigest()))
    C = 33
    eta = -a*pow(C,-1,q) % q
    actual = sum(c*d for z,c in supports[C].items() for k,d in G.items() if z*k % q == eta)
    frozen = sum(c*d for z,c in supports[21].items() for k,d in G.items() if z*k % q == eta)
    assert actual == 1 and frozen == 2
    return dict(q=q,R=R,K=K,a=a,b=b,receipts=receipts,
                frozen_C_counterexample=dict(actual_C=33,frozen_C=21,eta=eta,
                                             actual_primal=actual,frozen_primal=frozen),
                formula='P_C=(1/q^2)sum_{all h,l residues} Fhat_C(h)Ghat(l)Kloos(eta*h*b,l;q)',
                scope='Finite cyclic congruence benchmark only; not an assertion that original HH windows separate')


def run():
    inverse = [inverse_test(q,c) for q,c in ((11,11),(15,3),(100,5))]
    orbit = large_N_orbit_test()
    coupled = coupled_C_test()
    result = dict(status='PASS',arithmetic='Integer phase histograms and exact cyclotomic polynomial division',
                  inverse_completion=inverse,large_N_induced_character=orbit,coupled_C_h_benchmark=coupled,
                  formula='tau*H=q*Fchi-E_nonunit; tau^2*H*L/q^2=(Fchi-EF/q)*(Gchi-EG/q)',
                  limitations='No factorization of the original joint HH selectors; all nonunit h and collision diagonals retained; no global D_N or asymptotic moment bound',
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'inverse.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k] for k in ('status','inverse_completion','script_sha256')},indent=2))
    print(json.dumps(dict(large_N=N,tau_induced_mod5=orbit['tau_exact'],
                         coupled_C_counterexample=coupled['frozen_C_counterexample'],
                         energy_by_C={r['C']:r['energy']['energy'] for r in coupled['receipts']}),indent=2))


if __name__ == '__main__':
    run()
