"""Exact full Mobius-Lambda convolution and insertion into the raw profile.

All prime powers, p|l terms, l=1 and exact fronts are retained. Logarithms
are formal prime-log vectors. Divisions by log(m) are checked by multiplying
each fixed-m identity by its common positive denominator, never by floats.
"""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
from conservation import initialize,verify
from shared import (ROOT,N,factor,mu,actual_profile,vector_add,multiply_vectors,
                     polynomial_sign_certificate,log_vector,serialize)


def prime_power_terms(m):
    terms=[]
    for p,exponent in factor(m):
        d=1
        for j in range(1,exponent+1):
            d*=p
            ell=m//d
            terms.append(dict(p=p,j=j,d=d,ell=ell,mu_ell=mu(ell),p_divides_ell=ell%p==0))
    return terms


def convolution(m,with_profile=False):
    assert 1<m<N
    L=log_vector(m)
    terms=prime_power_terms(m)
    numerator={}
    for term in terms:
        vector_add(numerator,{(term['p'],):1},term['mu_ell'])
    assert numerator=={key:-mu(m)*c for key,c in L.items() if mu(m)*c}
    prime_only={}
    unfiltered_prime_only={}
    for term in terms:
        if term['j']==1:
            vector_add(unfiltered_prime_only,{(term['p'],):1},term['mu_ell'])
            if not term['p_divides_ell']:
                vector_add(prime_only,{(term['p'],):1},term['mu_ell'])
    # L2 follows after full prime-power cancellation; its p|ell exclusion
    # must not be dropped while replacing Lambda by just primes.
    assert prime_only==numerator
    if with_profile:
        F,_=actual_profile(m)
        actual=multiply_vectors(F,numerator)
        expected=multiply_vectors(F,L)
        expected={key:-mu(m)*c for key,c in expected.items() if mu(m)*c}
        assert actual==expected
    return terms,numerator


def prefix_receipt(X):
    direct,grouped={},{ }
    term_count=proper_powers=shared_prime=first_axis_not_squarefree=0
    for m in range(2,X+1):
        terms,numerator=convolution(m,True)
        term_count+=len(terms)
        proper_powers+=sum(t['j']>1 for t in terms)
        shared_prime+=sum(t['p_divides_ell'] for t in terms)
        F,meta=actual_profile(m)
        if F and mu(N-m)==0:first_axis_not_squarefree+=1
        vector_add(direct,F,mu(m))
        # Recover the common-denominator coefficient from the actual
        # convolution numerator, independently of the direct mu(m) sum.
        L=log_vector(m)
        first=next(iter(L))
        ratio=Fraction(numerator.get(first,0),L[first])
        assert numerator=={key:ratio*c for key,c in L.items() if ratio*c}
        vector_add(grouped,F,-ratio)
    assert direct==grouped and not actual_profile(1)[0]
    return dict(X=X,m_domain=[2,X],prime_power_terms=term_count,proper_power_terms=proper_powers,
                p_divides_ell_terms=shared_prime,active_first_axis_nonsquarefree=first_axis_not_squarefree,
                identity='S_X=-sum_(p^j*ell<=X) mu(ell)*log(p)/log(p^j*ell)*F_N(p^j*ell)',
                denominator_verification='Each fixed-m numerator is compared coefficientwise after multiplication by log(m)>0',
                symbolic_terms=len(direct),sum_certificate=polynomial_sign_certificate(direct),
                sum_sha256=sha256(json.dumps(serialize(direct),sort_keys=True).encode()).hexdigest(),
                outside_prefix_argument_count=N-1-X,exterior='Uncomputed, retained; no global D_N bound')


def diagnostic(m):
    terms,numerator=convolution(m,True)
    F,meta=actual_profile(m)
    certificate=polynomial_sign_certificate(F)
    result=dict(m=m,n=N-m,factor_m=factor(m),factor_n=factor(N-m),mu_m=mu(m),
                prime_power_terms=terms,convolution_log_coefficients=serialize(numerator),
                raw_profile_symbolic_terms=len(F),raw_profile_certificate=certificate)
    if len(factor(m))==1:
        p,e=factor(m)[0]
        result['fixed_denominator_rational_weights']=[dict(d=t['d'],ell=t['ell'],
            before_global_minus=str(Fraction(t['mu_ell'],e))) for t in terms]
    if m==311:
        assert terms==[dict(p=311,j=1,d=311,ell=1,mu_ell=1,p_divides_ell=False)]
        assert certificate['sign']=='POSITIVE'
        result['l_one_contribution']='-F_N(311) < 0, retained'
    if m in (841,10201):
        p=factor(m)[0][0]
        assert len(terms)==2 and numerator=={} and mu(m)==0 and F
        assert terms[0]['ell']==p and terms[0]['mu_ell']==-1 and terms[1]['ell']==1 and terms[1]['mu_ell']==1
        result['cancellation']='(-1/2 + 1/2)*F_N(m)=0 before the common global minus'
        result['dropping_proper_powers']='Leaves a nonzero spurious contribution because F_N(m) is nonzero'
        result['prime_only_without_p_divides_ell_exclusion']='False: the j=1 shared-prime term survives spuriously'
    if m==303:
        assert mu(m)==1 and len(terms)==2
        assert {t['p'] for t in terms}=={3,101}
        assert all(N%t['p'] for t in terms)
    return result


def run():
    initialize()
    # Independent exact coefficient identity on all 2<=m<=20000.
    all_terms=0
    for m in range(2,20001):all_terms+=len(convolution(m)[0])
    receipts=[prefix_receipt(X) for X in (303,1024)]
    diagnostics=[diagnostic(m) for m in (303,311,841,10201)]
    result=dict(status='PASS_IDENTITY_ONLY',N=N,alpha=100,Q=999999,
                exact_convolution='mu(m)*log(m)=-(mu*Lambda)(m), m>1',
                exact_reduced_prime_identity='After cancellation: S_X=-sum_(p*ell<=X,p not dividing ell) mu(ell)*log(p)/log(p*ell)*F_N(p*ell)',
                coefficient_domain=[2,20000],coefficient_cases=19999,prime_power_terms=all_terms,
                profile_prefix_receipts=receipts,diagnostics=diagnostics,
                raw_first_axis_mask='rho1 only; no added mu(N-m)^2',
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                limitations='Standard exact identity; no gain, no suppression of prime powers/shared prime factors/l=1, no global profile computed')
    (ROOT/'logarithmic.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,coefficient_cases=19999,prime_power_terms=all_terms,
        prefixes=[dict(X=v['X'],terms=v['prime_power_terms'],proper_powers=v['proper_power_terms']) for v in receipts],
        previous_artifacts=result['previous_artifacts'],script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':run()
