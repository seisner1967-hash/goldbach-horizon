"""Exact finite Katai coverage/Gram identity for the actual raw F_N profile.

No small-correlation hypothesis is made. Diagonals, p|m exclusions, prefix
faces and the exact coverage residual are retained. N=100000000 is fixed.
"""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from math import gcd
from pathlib import Path
import json

from exact_tools import (N,ROOT,factor,mu,actual_profile,parse_log_vector,
                         vector_add,multiply_vectors,polynomial_sign_certificate,
                         squarefree_divisor_expansion)
from conservation import initialize,verify
sys.path.insert(0,str(ROOT.parent/'numerical'))
from parity_checks import direct_HU


def serialize(vector):
    return {','.join(map(str,key)):f'{c.numerator}/{c.denominator}' for key,c in sorted(vector.items())}


def identities(X,P):
    assert 1<=X<N and P and all(factor(p)==((p,1),) for p in P)
    A=sum(X//p for p in P)
    a=Fraction(A,X)
    assert a>0
    S,R={},{ }
    covered,uncovered={},{ }
    Fnorm={}
    nonzero_uncovered=0
    for n in range(1,X+1):
        F,_=actual_profile(n)
        count=sum(n%p==0 for p in P)
        vector_add(S,F,mu(n))
        vector_add(R,F,mu(n)*(a-count))
        vector_add(covered,F,mu(n)*count)
        if count==0:
            vector_add(uncovered,F,mu(n))
            nonzero_uncovered+=bool(F)
        vector_add(Fnorm,multiply_vectors(F,F))
    M=X//min(P)
    T,G={},{ }
    Qsf=sum(mu(m)**2 for m in range(1,M+1))
    for m in range(1,M+1):
        B={}
        for p in P:
            if p*m<=X and m%p:
                vector_add(B,actual_profile(p*m)[0])
        vector_add(T,B,mu(m))
        vector_add(G,multiply_vectors(B,B),mu(m)**2)
    lhs={key:a*c for key,c in S.items()}
    rhs=dict(R)
    vector_add(rhs,T,-1)
    assert lhs==rhs
    assert covered=={key:-c for key,c in T.items()}
    E={}
    correlations={}
    expanded={}
    for p in P:
        Ep={}
        for m in range(1,X//p+1):
            if m%p:
                F=actual_profile(p*m)[0]
                vector_add(Ep,multiply_vectors(F,F),mu(m)**2)
        E[p]=Ep
        vector_add(expanded,Ep)
    for p,q in combinations(P,2):
        C={}
        for m in range(1,X//max(p,q)+1):
            if gcd(m,p*q)==1:
                Fp=actual_profile(p*m)[0]
                Fq=actual_profile(q*m)[0]
                vector_add(C,multiply_vectors(Fp,Fq),mu(m)**2)
        correlations[p,q]=C
        vector_add(expanded,C,2)
    assert G==expanded
    V=sum((a-sum(n%p==0 for p in P))**2 for n in range(1,X+1))
    V_floor=Fraction(A+2*sum(X//(p*q) for p,q in combinations(P,2)))-Fraction(A*A,X)
    assert V==V_floor
    # At the norm level: the support and diagonal identities are exact.
    # The requested bound is mathematical Cauchy-Schwarz; no empirically
    # small covariance is used to replace G by its off-diagonal part.
    norms=dict(F_squared_symbolic_terms=len(Fnorm),Gram_symbolic_terms=len(G),
               Q_squarefree=Qsf,V=f'{V.numerator}/{V.denominator}')
    result=dict(X=X,P=P,a=f'{a.numerator}/{a.denominator}',M=M,
                coverage_identity='a*S=-sum_m mu(m)B(m)+R',
                Gram_identity='G=sum_p E_p+2sum_{p<q}C_pq',
                actual_first_axis_mask='rho1 only: n>1 and gcd(n,N)=1; no mu(n)^2',
                norms=norms,diagonal_nonzero={str(p):bool(v) for p,v in E.items()},
                correlations={f'{p},{q}':dict(symbolic_terms=len(v),certificate=polynomial_sign_certificate(v))
                              for (p,q),v in correlations.items()},
                residual_symbolic_terms=len(R),uncovered_nonzero_profile_arguments=nonzero_uncovered,
                uncovered_symbolic_terms=len(uncovered),
                outside_prefix_argument_count=N-1-X,
                outside_prefix_mass='Retained as an uncomputed exterior term; no global D_N conclusion',
                S_certificate=polynomial_sign_certificate(S),
                S_sha256=sha256(json.dumps(serialize(S),sort_keys=True).encode()).hexdigest(),
                R_sha256=sha256(json.dumps(serialize(R),sort_keys=True).encode()).hexdigest())
    if P==(2,5):
        assert not T and not G and all(not v for v in E.values()) and all(not v for v in correlations.values())
        assert R=={key:a*c for key,c in S.items()}
        assert bool(R)
        result['zero_correlation_counterexample']='P={2,5}: all dilation profiles vanish by unit mask, but R=a*S carries the entire nonzero prefix mass'
    if X==303 and P==(2,5):
        assert a==Fraction(211,303)
        assert all(not actual_profile(m)[0] for m in range(1,303))
        expected={(7,101):Fraction(-1,2),(41,101):Fraction(-1,2),(101,348431):Fraction(-1,2)}
        assert S==expected
        assert R=={key:Fraction(-211,606) for key in expected}
        result['explicit_S303']=dict(S='-1/2*log(99999697)*log(101)',
                                    S_coefficients=serialize(S),R_coefficients=serialize(R),
                                    B='0',G='0',R='(211/303)*S303',
                                    only_nonzero_raw_argument=303)
    return result


def raw_HH_diagnostics():
    F,meta=actual_profile(311)
    assert factor(311)==((311,1),) and factor(N-311)==((113,1),(199,1),(4447,1))
    assert meta['D_minus_W']=={'3':'1/2','311':'-1/2'}
    certificate=polynomial_sign_certificate(F)
    assert certificate['sign']=='POSITIVE'
    assert direct_HU(1,2)[0]==direct_HU(311,2)[0]==0
    a,b,r,k=21,13,99999727,1
    n,m=a*b,r*k
    assert n+m==N and gcd(n,N)==1 and mu(n) and mu(m)
    assert all(m%p for p in (3,7,11,13))
    carrier=direct_HU(a,2)[0]*direct_HU(r,2)[0]
    assert carrier==4 and a<=m and b<=m and r>100
    assert actual_profile(N-1)[0]==actual_profile(N)[0]==actual_profile(0)[0]=={}
    p=9967
    square_n=p*p
    square_m=N-square_n
    square_F,square_meta=actual_profile(square_m)
    assert factor(p)==((p,1),) and factor(square_n)==((p,2),)
    assert factor(square_m)==((3,1),(11,1),(41,1),(487,1)) and mu(square_m)==1
    assert squarefree_divisor_expansion(square_n)==0
    square_certificate=polynomial_sign_certificate(square_F)
    assert square_certificate['sign']=='POSITIVE'
    assert parse_log_vector(square_meta['fII'])=={(9967,):Fraction(-1)}
    return dict(raw_prime_argument_311=dict(metadata=meta,certificate=certificate,HH_carrier=0,
                                          verdict='Raw F_N is not the HH carrier profile'),
                active_first_axis_prime_square=dict(n=square_n,m=square_m,
                    factor_n=factor(square_n),factor_m=factor(square_m),mu_m=1,mu_n_squared=0,
                    fII='-log(9967)',prefix=square_meta['prefix'],symbolic_terms=len(square_F),
                    polynomial_sha256=sha256(json.dumps(serialize(square_F),sort_keys=True).encode()).hexdigest(),
                    certificate=square_certificate,
                    verdict='Actual raw F_N and its mu(m)-weighted contribution are nonzero although mu(n)^2=0'),
                uncovered_HH_tuple=dict(a=a,b=b,r=r,k=k,n=n,m=m,P=[3,7,11,13],c_P=0,HH_carrier=carrier,
                                        positive_weight='4*log13*logr',
                                        verdict='Finite prime-dilation coverage misses a genuine positive HH tuple'),
                strict_terminal_faces='F(0)=F(N)=F(N-1)=0; the last value is removed by n>1')


def run():
    initialize()
    diagnostics=raw_HH_diagnostics()
    receipts=[identities(X,(3,7,11,13)) for X in (512,1024)]
    receipts.extend(identities(X,(2,5)) for X in (303,1024))
    result=dict(status='PASS',N=N,alpha=100,Q=999999,
                raw_profile_definition='rho1(N-m)*(Lambda(N-m)-log(N-m))*(D_alpha_Q(m)-W_alpha_Q(N-m,m)) with 0<m<N',
                finite_receipts=receipts,diagnostics=diagnostics,
                actual_log_arithmetic='Rational coefficients of symbolic prime logarithms; signs enclosed by rational artanh intervals',
                previous_artifacts=verify(),
                limitations='No small correlation assumed, no diagonal removed, no first-axis squarefree mask invented, no global profile or D_N computed',
                script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'katai.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='PASS',N=N,receipts=[dict(X=row['X'],P=row['P'],a=row['a'],
                                                      Gram_terms=row['norms']['Gram_symbolic_terms'],
                                                      residual_terms=row['residual_symbolic_terms']) for row in receipts],
                         previous_artifacts=result['previous_artifacts'],script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':
    run()
