"""Exact signed compensation, k=1 cancellation and squarefree switch.

N=100000000; domains are finite and explicit. The acquired analytical
payment for I is never relabelled as a numerical PASS. No Lean call.
"""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from hashlib import sha256
from math import gcd,isqrt,prod
from pathlib import Path
import json
from conservation import initialize,verify
from shared import (ROOT,N,factor,divisors,mu,actual_profile,vector_add,
    multiply_vectors,parse_log_vector,log_vector,serialize,polynomial_sign_certificate)
from shared import output_directory

ALPHA=100
Q=999999


def phi(n):
    return prod(p**(e-1)*(p-1) for p,e in factor(n))


def Lambda_N(n):
    if not 1<n<N or gcd(n,N)!=1:return {}
    fs=factor(n)
    return {(fs[0][0],):1} if len(fs)==1 else {}


def log_m_over_k(m,k):
    v=log_vector(m)
    vector_add(v,log_vector(k),-1)
    return v


def selected_recombination(E,label):
    raw,S_lambda,I={},{},{}
    P,M={},{}
    active_lambda=0
    k1_points=0
    harmonic_slots=0
    for m in E:
        F,meta=actual_profile(m)
        vector_add(raw,F,mu(m) if 1<=m<=N else 0)
        n=N-m
        if not 1<=m<=N-2 or gcd(m,N)!=1:continue
        if m==1:
            assert not F
            continue
        kernel=parse_log_vector(meta['D_minus_W'])
        lam=Lambda_N(n)
        vector_add(S_lambda,multiply_vectors(lam,kernel),mu(m))
        vector_add(I,multiply_vectors(log_vector(n),kernel),mu(m))
        prefix=min(Q,(m-1)//ALPHA)
        if prefix:
            # The k=1 entries of D and W are both -log(m), before
            # multiplication by the same outer rho1/Lambda/Mobius factors.
            assert 1 in meta['admitted_divisors'] and 1 in meta['admitted_harmonic_k']
            k1_points+=1
        if not lam:continue
        active_lambda+=1
        for k in divisors(m):
            if k>Q or ALPHA*k>=m:continue
            r=m//k
            assert mu(k)*mu(m)==mu(k)**2*mu(r)*int(gcd(k,r)==1)
            if gcd(r,k*N)==1:
                P.setdefault(k,{})
                vector_add(P[k],multiply_vectors(lam,log_vector(r)),mu(r))
        for k in range(1,prefix+1):
            harmonic_slots+=1
            if gcd(k,N)!=1 or gcd(n,k)!=1:continue
            M.setdefault(k,{})
            vector_add(M[k],multiply_vectors(lam,log_m_over_k(m,k)),mu(m))
    expected=dict(S_lambda)
    vector_add(expected,I,-1)
    assert raw==expected
    shifted={}
    for k,v in P.items():vector_add(shifted,v,-mu(k)**2)
    for k,v in M.items():vector_add(shifted,v,Fraction(mu(k),phi(k)))
    assert shifted==S_lambda
    assert P.get(1,{})==M.get(1,{})
    return dict(label=label,arguments=len(E),active_Lambda_arguments=active_lambda,
                identity='S_full(E)=S_Lambda(E)-I(E); the same selection indicator stays in P_k(E) and M_k(E)',
                shifted_identity='S_Lambda(E)=-sum_k mu(k)^2 P_k(E)+sum_k mu(k)/phi(k) M_k(E)',
                k1_pointwise_cancellations=k1_points,k1_P_equals_M=True,
                harmonic_slots=harmonic_slots,raw_terms=len(raw),S_Lambda_terms=len(S_lambda),I_terms=len(I),
                raw_certificate=polynomial_sign_certificate(raw),
                raw_sha256=sha256(json.dumps(serialize(raw),sort_keys=True).encode()).hexdigest(),
                S_Lambda_sha256=sha256(json.dumps(serialize(S_lambda),sort_keys=True).encode()).hexdigest(),
                I_sha256=sha256(json.dumps(serialize(I),sort_keys=True).encode()).hexdigest(),
                exterior='Every omitted m is uncomputed; no full D_N estimate')


def switch_checks():
    cases=0
    for k in range(1,129):
        for r in range(1,513):
            assert mu(k)*mu(k*r)==mu(k)**2*mu(r)*int(gcd(k,r)==1)
            cases+=1
    diagnostics=[]
    for k,r in ((1,101),(3,101),(3,303),(9,101),(29,29),(101,101),(3,101*101)):
        value=mu(k)*mu(k*r)
        diagnostics.append(dict(k=k,r=r,factor_k=factor(k),factor_r=factor(r),factor_product=factor(k*r),
                                gcd=gcd(k,r),left=value,right=mu(k)**2*mu(r)*int(gcd(k,r)==1)))
    return dict(k_domain=[1,128],r_domain=[1,512],cases=cases,diagnostics=diagnostics)


def squarefree_inner(r,K):
    physical_K=min(Q,(N-2)//r)
    assert r>ALPHA and gcd(r,N)==1 and 1<=K<=physical_K
    direct={}
    for k in range(1,K+1):
        if gcd(k,r)==1:vector_add(direct,Lambda_N(N-r*k),mu(k)**2)
    rad_r=prod(p for p,_ in factor(r))
    expanded={}
    v_slots=0
    for d in range(1,isqrt(K)+1):
        if gcd(d,r*N)!=1:continue
        for t in divisors(rad_r):
            assert gcd(d,t)==1
            bound=K//(d*d*t)
            for v in range(1,bound+1):
                vector_add(expanded,Lambda_N(N-r*d*d*t*v),mu(d)*mu(t))
                v_slots+=1
    assert direct==expanded
    no_one=dict(direct)
    vector_add(no_one,Lambda_N(N-r),-1)
    explicit={}
    for k in range(2,K+1):
        if gcd(k,r)==1:vector_add(explicit,Lambda_N(N-r*k),mu(k)**2)
    assert no_one==explicit
    return dict(r=r,K_tested=K,K_physical=physical_K,complete_k_domain=K==physical_K,
                identity='sum mu(k)^2 Lambda_N(N-r*k)1_(k,r)=sum_d mu(d)sum_(t|rad(r))mu(t)sum_v Lambda_N(N-r*d²*t*v)',
                d_restriction='gcd(d,r*N)=1',k1_removed_exactly=True,v_slots=v_slots,
                symbolic_terms=len(no_one),untested_k_count=physical_K-K,
                exterior='Untested k>K retained when K is truncated; no head or tail estimate claimed')


def run():
    initialize()
    prefixes=[selected_recombination(list(range(1,X+1)),f'prefix 1..{X}') for X in (303,1024)]
    special=(841,909,10201,30603,658911)
    selected=selected_recombination(list(special),'explicit isolated arguments 841,909,10201,30603,658911')
    diagnostics=[]
    for m in special:
        F,meta=actual_profile(m)
        diagnostics.append(dict(m=m,n=N-m,factor_m=factor(m),factor_n=factor(N-m),mu_m=mu(m),
                                mu_n_squared=mu(N-m)**2,raw_profile_active=bool(F),
                                Lambda_N=serialize(Lambda_N(N-m)),prefix=meta['prefix']))
    inner=[squarefree_inner(r,K) for r,K in ((101,128),(103,256),(213,256),(311,511),
                                             (707,128),(12577,128),(99999727,1))]
    # Genuine prime-power values outside the unit support stay excluded.
    off=[]
    for n in (2**26,5**11):
        m=N-n
        assert factor(n)[0][1]>1 and len(factor(n))==1 and gcd(n,N)>1
        assert not Lambda_N(n) and not actual_profile(m)[0]
        off.append(dict(n=n,m=m,factor_n=factor(n),unit_mask=False,Lambda_N='ZERO',raw='ZERO'))
    for m in (0,N-1,N):assert not actual_profile(m)[0]
    result=dict(status='PASS_EXACT_IDENTITIES_ONLY',N=N,alpha=ALPHA,Q=Q,
                acquired_I_payment='Not numerically tested: applies only within its supplied analytical hypotheses/onset; N=1e8 does not validate that onset',
                bridge='D_N=-S_Lambda+I+2max(e,0) after the supplied bridge; only finite algebra S_full=S_Lambda-I is checked here',
                finite_prefixes=prefixes,isolated_selection=selected,isolated_diagnostics=diagnostics,
                Mobius_switch=switch_checks(),squarefree_inner=inner,off_support_prime_powers=off,
                raw_first_axis_mask='rho1 only; proper prime powers on units remain, no added mu(n)^2',
                arithmetic='Integer Mobius/Lambda coefficients and rational symbolic prime logs; rational artanh sign enclosures',
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                limitations='Selected finite m/k domains, true fronts and units retained; no acquired analytical budget recomputed, no global signed bound')
    (output_directory()/'compensation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,prefixes=[v['label'] for v in prefixes],
                         isolated_arguments=len(special),switch_cases=result['Mobius_switch']['cases'],
                         squarefree_k_slots=sum(v['K_tested'] for v in inner),
                         previous_artifacts=result['previous_artifacts'],script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':run()
