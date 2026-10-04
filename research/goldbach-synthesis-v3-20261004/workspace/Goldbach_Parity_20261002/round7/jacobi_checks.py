"""Exact full-character reconstruction with nonunit remainders retained.

N=100000000. Finite character phases are integral polynomials modulo the
exact cyclotomic polynomial. Complete unweighted Jacobi means never replace
the actual weighted HH tuple sum.
"""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path
import json
from conservation import initialize,verify
from shared import (ROOT,BASE,N,factor,mu,vector_add,multiply_vectors,
                     log_vector,serialize,polynomial_sign_certificate)
sys.path.insert(0,str(BASE/'round4'))
from inverse_checks import reduce_phases
sys.path.insert(0,str(BASE/'round6'))
from squarefree_checks import physical_point,compatible_CRT,enumerate_class


def primitive_logs(p):
    assert factor(p)==((p,1),)
    for g in range(2,p):
        logs={}
        for k in range(p-1):logs[pow(g,k,p)]=k
        if len(logs)==p-1:return g,logs
    raise AssertionError('No primitive generator found')


def phase(logs,j,x,L):
    return None if x% (L+1)==0 else j*logs[x%(L+1)]%L


def twist_phase(p,logs,j,n,m):
    if n%p==0 or m%p==0:return None
    return j*(logs[n%p]-logs[m%p])%(p-1)


def phase_polynomial(L,exponent,coefficient=1):
    result=[0]*L
    if exponent is not None:result[exponent%L]=coefficient
    return result


def jacobi_complete(p,C):
    assert N%p and C%p
    g,logs=primitive_logs(p)
    L=p-1
    receipts=[]
    reconstructed=[0]*L
    for j in range(1,L):
        hist=[0]*L
        without_C=[0]*L
        for z in range(p):
            exponent=twist_phase(p,logs,j,N-C*z,C*z)
            if exponent is not None:
                hist[exponent]+=1
                without_C[(exponent+j*logs[C%p])%L]+=1
        expected=phase_polynomial(L,j*logs[p-1],-1)
        assert reduce_phases(hist,L)==reduce_phases(expected,L)
        expected_no_C=phase_polynomial(L,j*logs[(-C)%p],-1)
        assert reduce_phases(without_C,L)==reduce_phases(expected_no_C,L)
        for exponent,c in enumerate(hist):
            reconstructed[(exponent-j*logs[p-1])%L]-=c
        if j==L//2 or (L%4==0 and j==L//4):
            receipts.append(dict(character_index=j,order=2 if j==L//2 else 4,
                Jacobi_reduced=list(reduce_phases(hist,L)),expected='-chi(-1)',
                without_C_reduced=list(reduce_phases(without_C,L)),without_C_expected='-chi(-C)'))
    principal_count=sum((N-C*z)%p!=0 and (C*z)%p!=0 for z in range(p))
    assert principal_count==p-2
    assert reduce_phases(reconstructed,L)==(p-2,)
    return dict(p=p,C=C,generator=g,all_nonprincipal_characters=L-1,
                quadratic_order4_receipts=receipts,principal_count=principal_count,
                reconstructed_complete_sum=p-2,verdict='Exact reconstruction of the p-2 principal terms; no saving')


def centered_prefixes(p,C):
    assert N%p and C%p
    g,logs=primitive_logs(p)
    L=p-1
    cases=0
    max_discrepancy=Fraction(0)
    for z in range(p):
        reconstructed=[Fraction(0)]*L
        for j in range(1,L):
            exponent=twist_phase(p,logs,j,N-C*z,C*z)
            if exponent is not None:reconstructed[(exponent-j*logs[p-1])%L]-=1
            reconstructed[0]-=Fraction(1,p)
        indicator=int((N-C*z)%p!=0 and (C*z)%p!=0)
        expected=Fraction(indicator)-Fraction(p-2,p)
        reduced=reduce_phases(reconstructed,L)
        assert reduced==((expected,) if expected else ())
    # Every offset, every unit slope, and every prefix up to three periods.
    for offset in range(p):
        for slope in range(1,p):
            discrepancy=Fraction(0)
            for length in range(0,3*p+1):
                assert abs(discrepancy)<=2
                max_discrepancy=max(max_discrepancy,abs(discrepancy))
                cases+=1
                z=offset+slope*length
                discrepancy+=Fraction(int((N-C*z)%p!=0 and (C*z)%p!=0))-Fraction(p-2,p)
    constant_indicator=int((N-C)%p!=0 and C%p!=0)
    constant_discrepancy=Fraction(3*p)*(Fraction(constant_indicator)-Fraction(p-2,p))
    assert abs(constant_discrepancy)>2
    return dict(p=p,C=C,prefix_cases=cases,max_absolute_discrepancy=str(max_discrepancy),
                exact_bound='<=2 for p not dividing progression slope',
                nonunit_slope_exception=dict(slope=p,offset=1,length=3*p,
                    discrepancy=str(constant_discrepancy),verdict='Constant residue; the <=2 assertion does not apply'))


def tuple_weight(point):
    r=point['s']*point['t']*point['zeta']
    return {key:point['four_Mobius_product']*c for key,c in
            multiply_vectors(log_vector(point['b']),log_vector(r)).items()}


def weighted_HH_reconstruction(points,p):
    g,logs=primitive_logs(p)
    L=p-1
    full,remainder,principal={},{},{}
    weighted_phases={}
    exception_sites=[]
    unit_sites=[]
    for point in points:
        W=tuple_weight(point)
        vector_add(full,W)
        n,m=point['n'],point['m']
        if n%p==0 or m%p==0:
            vector_add(remainder,W)
            exception_sites.append(dict(n=n,m=m,q_divides_n=n%p==0,q_divides_m=m%p==0,
                                        Mobius_product=point['four_Mobius_product']))
            for j in range(1,L):assert twist_phase(p,logs,j,n,m) is None
            continue
        vector_add(principal,W)
        unit_sites.append(dict(n=n,m=m))
        # All original multiplicative character factors, including x/zeta.
        first=(point['b'],point['u'],point['v'],point['x'])
        second=(point['k'],point['s'],point['t'],point['zeta'])
        for j in range(1,L):
            exponent=twist_phase(p,logs,j,n,m)
            expanded=j*(sum(logs[v%p] for v in first)-sum(logs[v%p] for v in second))%L
            assert expanded==exponent
            shifted=(exponent-j*logs[p-1])%L
            for key,c in W.items():
                weighted_phases.setdefault(key,[0]*L)[shifted]-=c
    compare={}
    for key,hist in weighted_phases.items():
        reduced=reduce_phases(hist,L)
        expected=principal.get(key,0)
        assert reduced==((expected,) if expected else ())
        if expected:compare[key]=expected
    assert compare==principal
    summed=dict(remainder)
    vector_add(summed,compare)
    assert summed==full
    original=points[0]
    if p==13:
        assert original['n']==273 and original['m']==99999727 and original['four_Mobius_product']==1
        assert original['n']%13==0 and tuple_weight(original)
        assert remainder
    return dict(p=p,Omega=len(points),Omega_p=len(unit_sites),nonunit_sites=exception_sites,
                identity='S_HH=R_p+T0 ; T0=-sum_(chi nonprincipal) conj(chi(-1))*Tchi',
                R_symbolic_terms=len(remainder),R_certificate=polynomial_sign_certificate(remainder),
                S_symbolic_terms=len(full),S_certificate=polynomial_sign_certificate(full),
                principal_weighted_terms=len(principal),all_character_factors_preserved=True,
                weight='mu(u)mu(v)mu(s)mu(t)*log(b)*log(s*t*zeta), original finite tuple selection',
                verdict='Nonunit remainder retained; complete unweighted Jacobi means are not substituted for these weights')


def actual_CRT_twists():
    A,C=273,10403
    hi=(N-A)//C
    cell=compatible_CRT(A,C,1,3,1,1)
    points=enumerate_class(cell,1,hi)
    assert cell['M']==819 and len(points)==12 and gcd(cell['M'],11)==1
    g,logs=primitive_logs(11)
    values=[]
    for z in points:
        n=N-C*z
        assert n%A==n%9==0
        exponent=twist_phase(11,logs,5,n,C*z)
        value=0 if exponent is None else (1 if exponent==0 else -1)
        values.append(dict(zeta=z,n=n,m=C*z,quadratic_full_twist=value,
                           q_unit=n%11!=0 and C*z%11!=0))
    assert any(v['quadratic_full_twist']==0 for v in values)
    assert any(v['quadratic_full_twist']==1 for v in values)
    assert any(v['quadratic_full_twist']==-1 for v in values)
    return dict(p=11,A=A,C=C,CRT=cell,J=[1,hi],points=values,
                interpretation='Signed e=3 expansion cells, not SF HH points; p-unit exceptions remain')


def run():
    initialize()
    primes=(3,7,11,13,17,19)
    complete=[jacobi_complete(p,10403) for p in primes]
    centered=[centered_prefixes(p,10403) for p in primes]
    points=[physical_point(13,3,7,1,7951,12577,1),
            physical_point(13,3,75469,1,7717,12577,1),
            physical_point(13,3,7,1,11,17,43063),
            physical_point(13,3,7,1,11,17,44701),
            physical_point(101,103,107,1,3,71,244769)]
    assert all(points)
    weighted=[weighted_HH_reconstruction(points,p) for p in primes]
    # The old conductor-dividing-N case remains a separate constant sector.
    _,logs5=primitive_logs(5)
    for j in range(1,4):
        for z in (1,3,7,9):
            assert twist_phase(5,logs5,j,N-10403*z,10403*z)==j*logs5[4]%4
    result=dict(status='PASS_IDENTITIES_ONLY',N=N,complete_Jacobi=complete,
                centered_prefixes=centered,centered_prefix_cases=sum(v['prefix_cases'] for v in centered),
                actual_HH_points=points,weighted_reconstruction=weighted,CRT_twists=actual_CRT_twists(),
                conductor_divides_N_baseline='q=5: full twist constant chi(-1) on q units; kept distinct',
                arithmetic='Integer phase polynomials modulo exact cyclotomic polynomials, rational centering; no complex floating approximation',
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                limitations='Exactly five admissible HH tuples and stated finite CRT cells, not global HH support; no asymptotic gain or D_N bound')
    (ROOT/'jacobi.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,HH_tuples=len(points),primes=list(primes),
                         centered_prefix_cases=result['centered_prefix_cases'],previous_artifacts=result['previous_artifacts'],
                         script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':run()
