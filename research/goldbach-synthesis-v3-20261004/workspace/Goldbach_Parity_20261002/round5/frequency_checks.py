"""Exact frequency strata, induced Gauss, and nonreal-character filter.

N=100000000 is a real parameter. Large group identities use explicit orbit
arguments; smaller diagnostics use complete integer cyclotomic histograms.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction
from hashlib import sha256
from math import gcd, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
sys.path.insert(0,str(BASE/'numerical'))
sys.path.insert(0,str(BASE/'round4'))
from parity_checks import N, factor, divisors, mu
from inverse_checks import reduce_phases,cyclic_convolution,add,character
from conservation import initialize,verify


def phi(n):
    return prod(p**(e-1)*(p-1) for p,e in factor(n))


def scalar(poly,c):
    return [c*x for x in poly]


def conjugate(poly,q):
    out = [0]*q
    for i,c in enumerate(poly):
        out[-i % q] += c
    return out


def gauss(chi,h,q):
    out = [0]*q
    for x,c in enumerate(chi):
        out[h*x % q] += c
    return out


def normalize_constant(poly,q):
    reduced = reduce_phases(poly,q)
    assert len(reduced) <= 1
    return reduced[0] if reduced else 0


def phase_reduction_test():
    qs = divisors(N)
    assert len(qs)==81 and sum(phi(q) for q in qs)==N
    checks = 0
    sampled_h = set()
    for q in qs:
        a_values = {0} if q==1 else {a for a in range(1,min(q,258)) if gcd(a,q)==1}
        if q>1:
            a_values.add(q-1)
        for a in a_values:
            h = (N//q)*a
            assert 0 <= h < N and gcd(h,N)==N//q
            assert h not in sampled_h
            sampled_h.add(h)
            for x in (-N+1,-11,-1,0,1,2,3,5,7,11,73,N-1):
                assert Fraction(h*x,N)==Fraction(a*x,q)
                checks += 1
    return dict(N=N,divisor_strata=len(qs),exact_total_stratum_cardinality=N,
                phase_checks=checks,sampled_distinct_frequencies=len(sampled_h),
                a_domain='Every unit a<min(q,258), plus a=q-1; q=1 uses a=0',
                x_values=[-N+1,-11,-1,0,1,2,3,5,7,11,73,N-1],
                identity='h=(N/q)a gives exactly hx/N=ax/q as rational numbers',
                scope='Every divisor q of N is used; a frequencies beyond the stated sample are covered algebraically, not enumerated')


def large_N_gauss_support():
    assert factor(N)==((2,8),(5,8)) and phi(N)==40000000
    step = N//10
    classes = (1,3,7,9)
    chi5 = {x:1 if pow(x%5,2,5)==1 else -1 for x in classes}
    tau5 = [0]*10
    for x in range(1,5):
        tau5[2*x % 10] += 1 if pow(x,2,5)==1 else -1
    assert normalize_constant(cyclic_convolution(tau5,conjugate(tau5,10),10),10)==5
    active = []
    contributions = {5:[0]*10,10:[0]*10}
    for t in range(10):
        local = [0]*10
        for x in classes:
            local[t*x % 10] += chi5[x]
        reduced = reduce_phases(local,10)
        h = step*t
        q = N//gcd(h,N)
        if t in (0,5):
            assert not reduced
            continue
        assert q in (5,10)
        a = h//(N//q)
        chi_a = 1 if pow(a%5,2,5)==1 else -1
        assert reduce_phases(local,10)==reduce_phases(scalar(tau5,chi_a),10)
        norm = normalize_constant(cyclic_convolution(scalar(local,step),conjugate(scalar(local,step),10),10),10)
        assert norm==5*step*step
        active.append(dict(h=h,q=q,a=a,Gauss_coefficient_times_tau5=step*chi_a,normSq=norm))
        # F=delta1: Fhat(h)=e_N(-h)=e_10(-t).
        for phase,c in enumerate(local):
            contributions[q][(phase-t)%10] += step*c
    stratum = {q:normalize_constant(value,10) for q,value in contributions.items()}
    assert stratum=={5:50000000,10:50000000}
    F = {1:2,3:-1,7:3,9:1,11:-2,N-1:1}
    Fchi = sum(c*(1 if pow(z%5,2,5)==1 else -1) for z,c in F.items())
    for q in (5,10):
        projected = [0]*10
        for item in active:
            if item['q']!=q:
                continue
            t=item['h']//step
            for z,c in F.items():
                for x in classes:
                    projected[t*(x-z)%10] += step*c*chi5[x]
        assert normalize_constant(projected,10)==50000000*Fchi
    return dict(N=N,primitive_conductor=5,unit_count=phi(N),unit_classes_mod10=classes,
                orbit_identity='x=r+10j, j=0..N/10-1; the geometric orbit vanishes unless N/10 divides h',
                active_frequency_count=len(active),active=active,
                F_delta1_stratum_contributions=stratum,
                total_nonunit_remainder=N,unit_frequency_tau=0,
                general_unit_support_F=F,general_Fchi=Fchi,
                general_stratum_coefficient_each=50000000,
                distinction='Conductor 5 is distinct from q. Only q=5,10 are active here because N has high powers of 2 and 5.',
                scope='Five/ten-phase and geometric-orbit certificate; no enumeration of 100000000 frequencies or 40000000 units')


def direct_small_strata(modulus,r):
    chi = character(modulus,r)
    units = tuple(x for x in range(modulus) if gcd(x,modulus)==1)
    records=[]
    for q in divisors(modulus):
        a_values = (0,) if q==1 else tuple(a for a in range(1,q) if gcd(a,q)==1)
        phases=[0]*modulus
        for a in a_values:
            h=(modulus//q)*a
            for x in units:
                phases[h*(x-1)%modulus] += chi[x]
        actual=normalize_constant(phases,modulus)
        c=q//r if q%r==0 else None
        active=c is not None and mu(c)!=0 and gcd(c,r)==1
        expected=r*phi(modulus)//phi(q) if active else 0
        assert actual==expected
        # Also test g_N((N/q)a) by descent for representative unit a.
        for a in ({0} if q==1 else {1,q-1}):
            h=(modulus//q)*a
            direct=gauss(chi,h,modulus)
            if q%r:
                expected_hist=[0]*modulus
            else:
                expected_hist=[0]*modulus
                chi_q=character(q,r)
                multiplier=phi(modulus)//phi(q)
                chi_a=1 if pow(a%r,(r-1)//2,r)==1 else -1
                for x,weight in enumerate(chi_q):
                    expected_hist[(modulus//q)*x % modulus] += multiplier*chi_a*weight
            assert reduce_phases(direct,modulus)==reduce_phases(expected_hist,modulus)
        records.append(dict(q=q,active=active,frequency_count=len(a_values),F_delta1_contribution=actual))
    tau=gauss(chi,1,modulus)
    kappa=normalize_constant(cyclic_convolution(tau,conjugate(tau,modulus),modulus),modulus)
    assert sum(item['F_delta1_contribution'] for item in records)==modulus
    assert next(item['F_delta1_contribution'] for item in records if item['q']==modulus)==kappa
    return dict(N=modulus,conductor=r,strata=records,kappa=kappa,
                exact_nonunit_remainder_delta1=modulus-kappa,
                scope='All frequencies and all units enumerated only for this stated small modulus')


def large_reduced_module_counterexample():
    modulus,r,q,h = 70630,5,35315,2
    assert factor(modulus)==((2,1),(5,1),(7,1),(1009,1))
    assert q==modulus//gcd(h,modulus) and q==modulus//2
    c=q//r
    assert mu(c)==1 and gcd(c,r)==1
    chi_c=1 if pow(c%5,2,5)==1 else -1
    assert chi_c==-1
    assert phi(modulus)//phi(q)==1
    for x in (-11,0,1,7,73,modulus-1):
        assert Fraction(h*x,modulus)==Fraction(x,q)
    return dict(N=modulus,conductor=r,h=h,q=q,nonunit_frequency=True,
                primitive_Gauss_factor=mu(c)*chi_c,Gauss_normSq=5,
                F_delta1_stratum_contribution=5,
                verdict='Small conductor does not imply a small reduced module for a nonzero nonunit frequency',
                scope='Separate arithmetic benchmark; Gauss nonvanishing uses the exact induced-character factor and primitive five-phase Gauss, not enumeration of q frequencies')


def order4_test(modulus):
    assert modulus in (5,10)
    Q=20
    phase_scale=Q//modulus
    k={1:0,2:1,4:2,3:3}
    units=tuple(x for x in range(modulus) if gcd(x,modulus)==1)
    tau,tau_inverse=[0]*Q,[0]*Q
    for x in units:
        tau[(phase_scale*x+5*k[x%5])%Q] += 1
        tau_inverse[(phase_scale*x-5*k[x%5])%Q] += 1
    prefactor=[0]*Q
    prefactor[10]=1 # chi^{-1}(-1)=-1.
    assert reduce_phases(tau_inverse,Q)==reduce_phases(cyclic_convolution(prefactor,conjugate(tau,Q),Q),Q)
    kappa_poly=cyclic_convolution(prefactor,cyclic_convolution(tau_inverse,tau,Q),Q)
    kappa=normalize_constant(kappa_poly,Q)
    norm=normalize_constant(cyclic_convolution(tau,conjugate(tau,Q),Q),Q)
    assert kappa==norm==5
    assert reduce_phases(tau,Q)!=reduce_phases(tau_inverse,Q)

    def axis(F,unit_hypothesis=True):
        if unit_hypothesis:
            assert all(gcd(z,modulus)==1 for z in F)
        H,M,E=[0]*Q,[0]*Q,[0]*Q
        for z,c in F.items():
            if gcd(z,modulus)==1:
                M[-5*k[z%5]%Q] += c
        for h in range(modulus):
            hat=[0]*Q
            for z,c in F.items():
                hat[-phase_scale*h*z%Q] += c
            if gcd(h,modulus)==1:
                shifted=[0]*Q
                for phase,c in enumerate(hat):
                    shifted[(phase+5*k[h%5])%Q] += c
                add(H,shifted)
            else:
                g=[0]*Q
                for x in units:
                    g[(phase_scale*h*x-5*k[x%5])%Q] += 1
                add(E,cyclic_convolution(hat,g,Q))
        if unit_hypothesis:
            correct=cyclic_convolution(prefactor,cyclic_convolution(tau,M,Q),Q)
            assert reduce_phases(H,Q)==reduce_phases(correct,Q)
            assert reduce_phases(cyclic_convolution(tau_inverse,H,Q),Q)==reduce_phases(scalar(M,kappa),Q)
            assert reduce_phases(E,Q)==reduce_phases(scalar(M,modulus-kappa),Q)
        return H,M,E

    F,G={1:2,2:-1,3:3,4:1},{1:-1,2:2,3:1,4:-2}
    if modulus==10:
        F,G={1:2,7:-1,3:3,9:1},{1:-1,7:2,3:1,9:-2}
    H,M,E=axis(F)
    L,M_G,E_G=axis(G)
    lhs=cyclic_convolution(cyclic_convolution(tau_inverse,H,Q),cyclic_convolution(tau_inverse,L,Q),Q)
    rhs=scalar(cyclic_convolution(M,M_G,Q),kappa*kappa)
    assert reduce_phases(lhs,Q)==reduce_phases(rhs,Q)
    H_one,M_one,_=axis({1:1})
    wrong=cyclic_convolution(prefactor,cyclic_convolution(tau_inverse,M_one,Q),Q)
    assert reduce_phases(H_one,Q)!=reduce_phases(wrong,Q)
    dropped_unit=None
    if modulus==10:
        nonunit_H,nonunit_M,_=axis({2:1},False)
        assert reduce_phases(nonunit_M,Q)==() and reduce_phases(nonunit_H,Q)!=()
        dropped_unit=dict(F='delta2',gcd_2_modulus=2,primal_character_pairing=0,
                          actual_H_reduced=reduce_phases(nonunit_H,Q),
                          verdict='FALSE if the unit-support hypothesis is omitted')
    return dict(N=modulus,conductor=5,character='Order 4 with chi(2)=i',phase_modulus=Q,
                tau_chi_reduced=reduce_phases(tau,Q),tau_inverse_reduced=reduce_phases(tau_inverse,Q),
                kappa=kappa,normSq_tau=kappa,
                H_formula='H=chi^{-1}(-1)*tau(chi)*FbarChi; the completion multiplier is tau(chi^{-1})',
                FbarChi_reduced=reduce_phases(M,Q),FbarChi_is_not_assumed_real_or_positive=True,
                scalar_double_unit_projection=f'{kappa*kappa}/{modulus*modulus}',
                wrong_same_Gauss_counterexample=True,dropped_unit_support_counterexample=dropped_unit)


def run():
    initialize()
    phase=phase_reduction_test()
    large=large_N_gauss_support()
    small=[direct_small_strata(n,r) for n,r in ((15,3),(100,5),(385,5))]
    nonreal=[order4_test(n) for n in (5,10)]
    result=dict(status='PASS',phase_reduction=phase,large_N_gauss=large,
                direct_small_strata=small,order4_character_filter=nonreal,
                large_reduced_module_counterexample=large_reduced_module_counterexample(),
                central_convention='tau(psi)=sum_units psi(x)e_N(x); tau(chi) and tau(chi^{-1}) remain distinct',
                central_identity='H=chi^{-1}(-1)tau(chi)FbarChi; kappa=chi^{-1}(-1)tau(chi^{-1})tau(chi)=normSq(tau(chi)); E=(N-kappa)FbarChi on unit support',
                limitations='Exact finite and orbit diagnostics only; no global D_N, no positivity asserted for complex FbarChi, no automatic small-reduced-module inference',
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'frequency.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='PASS',N=N,phase_checks=phase['phase_checks'],divisor_strata=phase['divisor_strata'],
                         active_Gauss_frequencies=large['active_frequency_count'],
                         stratum_contributions=large['F_delta1_stratum_contributions'],
                         order4=[dict(N=row['N'],kappa=row['kappa'],two_Gauss_distinct=True) for row in nonreal],
                         previous_artifacts=result['previous_artifacts'],script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':
    run()
